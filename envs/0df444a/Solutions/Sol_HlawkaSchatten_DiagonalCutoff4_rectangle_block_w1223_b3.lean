-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1223_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:12:15.944437+00:00
-- url     : https://prove2.me/submissions/a79af583-158d-4463-9982-4bbd88645fde

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
theorem support_rectangle_w1223_box_0 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2004454023/10000000000 : ℝ)*x 0 + (537512853/1000000000 : ℝ)*x 1 + (5375128619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2004454023/10000000000 : ℝ)^263 ≤ (11953977456689/100000000000000 : ℝ)^199 := by
    have hnat : (2004454023 : ℕ)^263*100000000000000^199 ≤ 11953977456689^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004454023 10000000000 11953977456689 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537512853/1000000000 : ℝ)^263 ≤ (550287634803/1250000000000 : ℝ)^199 := by
    have hnat : (537512853 : ℕ)^263*1250000000000^199 ≤ 550287634803^199*1000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537512853 1000000000 550287634803 1250000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375128619/10000000000 : ℝ)^263 ≤ (44023011747589/100000000000000 : ℝ)^199 := by
    have hnat : (5375128619 : ℕ)^263*100000000000000^199 ≤ 44023011747589^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375128619 10000000000 44023011747589 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2004454023/10000000000 : ℝ), (537512853/1000000000 : ℝ), (5375128619/10000000000 : ℝ)] ![(11953977456689/100000000000000 : ℝ), (550287634803/1250000000000 : ℝ), (44023011747589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2004454023/10000000000 : ℝ)|^263 ≤ (11953977456689/100000000000000 : ℝ)^199
        have hw : |(-2004454023/10000000000 : ℝ)|=(2004454023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(537512853/1000000000 : ℝ)|^263 ≤ (550287634803/1250000000000 : ℝ)^199
        have hw : |(537512853/1000000000 : ℝ)|=(537512853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375128619/10000000000 : ℝ)|^263 ≤ (44023011747589/100000000000000 : ℝ)^199
        have hw : |(5375128619/10000000000 : ℝ)|=(5375128619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_box_1 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5296658991/10000000000 : ℝ)*x 0 + (-422212861/2000000000 : ℝ)*x 1 + (2687564059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296658991/10000000000 : ℝ)^263 ≤ (43175645722627/100000000000000 : ℝ)^199 := by
    have hnat : (5296658991 : ℕ)^263*100000000000000^199 ≤ 43175645722627^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296658991 10000000000 43175645722627 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422212861/2000000000 : ℝ)^263 ≤ (12801347936741/100000000000000 : ℝ)^199 := by
    have hnat : (422212861 : ℕ)^263*100000000000000^199 ≤ 12801347936741^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422212861 2000000000 12801347936741 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687564059/5000000000 : ℝ)^263 ≤ (44023006324693/100000000000000 : ℝ)^199 := by
    have hnat : (2687564059 : ℕ)^263*100000000000000^199 ≤ 44023006324693^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687564059 5000000000 44023006324693 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296658991/10000000000 : ℝ), (-422212861/2000000000 : ℝ), (2687564059/5000000000 : ℝ)] ![(43175645722627/100000000000000 : ℝ), (12801347936741/100000000000000 : ℝ), (44023006324693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296658991/10000000000 : ℝ)|^263 ≤ (43175645722627/100000000000000 : ℝ)^199
        have hw : |(5296658991/10000000000 : ℝ)|=(5296658991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422212861/2000000000 : ℝ)|^263 ≤ (12801347936741/100000000000000 : ℝ)^199
        have hw : |(-422212861/2000000000 : ℝ)|=(422212861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687564059/5000000000 : ℝ)|^263 ≤ (44023006324693/100000000000000 : ℝ)^199
        have hw : |(2687564059/5000000000 : ℝ)|=(2687564059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_box_2 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (529665883/1000000000 : ℝ)*x 0 + (1075025671/2000000000 : ℝ)*x 1 + (-2111064201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529665883/1000000000 : ℝ)^263 ≤ (43175643988163/100000000000000 : ℝ)^199 := by
    have hnat : (529665883 : ℕ)^263*100000000000000^199 ≤ 43175643988163^199*1000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529665883 1000000000 43175643988163 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075025671/2000000000 : ℝ)^263 ≤ (8804601778003/20000000000000 : ℝ)^199 := by
    have hnat : (1075025671 : ℕ)^263*20000000000000^199 ≤ 8804601778003^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075025671 2000000000 8804601778003 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111064201/10000000000 : ℝ)^263 ≤ (1280134710327/10000000000000 : ℝ)^199 := by
    have hnat : (2111064201 : ℕ)^263*10000000000000^199 ≤ 1280134710327^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111064201 10000000000 1280134710327 10000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529665883/1000000000 : ℝ), (1075025671/2000000000 : ℝ), (-2111064201/10000000000 : ℝ)] ![(43175643988163/100000000000000 : ℝ), (8804601778003/20000000000000 : ℝ), (1280134710327/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529665883/1000000000 : ℝ)|^263 ≤ (43175643988163/100000000000000 : ℝ)^199
        have hw : |(529665883/1000000000 : ℝ)|=(529665883/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075025671/2000000000 : ℝ)|^263 ≤ (8804601778003/20000000000000 : ℝ)^199
        have hw : |(1075025671/2000000000 : ℝ)|=(1075025671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2111064201/10000000000 : ℝ)|^263 ≤ (1280134710327/10000000000000 : ℝ)^199
        have hw : |(-2111064201/10000000000 : ℝ)|=(2111064201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_box_3 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1115025729/2500000000 : ℝ)*x 0 + (2151041863/5000000000 : ℝ)*x 1 + (4302084153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1115025729/2500000000 : ℝ)^263 ≤ (6880204862917/20000000000000 : ℝ)^199 := by
    have hnat : (1115025729 : ℕ)^263*20000000000000^199 ≤ 6880204862917^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115025729 2500000000 6880204862917 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2151041863/5000000000 : ℝ)^263 ≤ (32799485685073/100000000000000 : ℝ)^199 := by
    have hnat : (2151041863 : ℕ)^263*100000000000000^199 ≤ 32799485685073^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151041863 5000000000 32799485685073 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4302084153/10000000000 : ℝ)^263 ≤ (32799489987551/100000000000000 : ℝ)^199 := by
    have hnat : (4302084153 : ℕ)^263*100000000000000^199 ≤ 32799489987551^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302084153 10000000000 32799489987551 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1115025729/2500000000 : ℝ), (2151041863/5000000000 : ℝ), (4302084153/10000000000 : ℝ)] ![(6880204862917/20000000000000 : ℝ), (32799485685073/100000000000000 : ℝ), (32799489987551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1115025729/2500000000 : ℝ)|^263 ≤ (6880204862917/20000000000000 : ℝ)^199
        have hw : |(1115025729/2500000000 : ℝ)|=(1115025729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2151041863/5000000000 : ℝ)|^263 ≤ (32799485685073/100000000000000 : ℝ)^199
        have hw : |(2151041863/5000000000 : ℝ)|=(2151041863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4302084153/10000000000 : ℝ)|^263 ≤ (32799489987551/100000000000000 : ℝ)^199
        have hw : |(4302084153/10000000000 : ℝ)|=(4302084153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_box_4 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-563603859/2500000000 : ℝ)*x 0 + (5282086883/10000000000 : ℝ)*x 1 + (2641043493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (563603859/2500000000 : ℝ)^263 ≤ (6981270570421/50000000000000 : ℝ)^199 := by
    have hnat : (563603859 : ℕ)^263*50000000000000^199 ≤ 6981270570421^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563603859 2500000000 6981270570421 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282086883/10000000000 : ℝ)^263 ≤ (5377341108839/12500000000000 : ℝ)^199 := by
    have hnat : (5282086883 : ℕ)^263*12500000000000^199 ≤ 5377341108839^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282086883 10000000000 5377341108839 12500000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641043493/5000000000 : ℝ)^263 ≤ (8603745995871/20000000000000 : ℝ)^199 := by
    have hnat : (2641043493 : ℕ)^263*20000000000000^199 ≤ 8603745995871^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641043493 5000000000 8603745995871 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-563603859/2500000000 : ℝ), (5282086883/10000000000 : ℝ), (2641043493/5000000000 : ℝ)] ![(6981270570421/50000000000000 : ℝ), (5377341108839/12500000000000 : ℝ), (8603745995871/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-563603859/2500000000 : ℝ)|^263 ≤ (6981270570421/50000000000000 : ℝ)^199
        have hw : |(-563603859/2500000000 : ℝ)|=(563603859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282086883/10000000000 : ℝ)|^263 ≤ (5377341108839/12500000000000 : ℝ)^199
        have hw : |(5282086883/10000000000 : ℝ)|=(5282086883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641043493/5000000000 : ℝ)|^263 ≤ (8603745995871/20000000000000 : ℝ)^199
        have hw : |(2641043493/5000000000 : ℝ)|=(2641043493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_box_5 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (268113709/500000000 : ℝ)*x 0 + (-2147895741/10000000000 : ℝ)*x 1 + (2641043397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268113709/500000000 : ℝ)^263 ≤ (10970981746057/25000000000000 : ℝ)^199 := by
    have hnat : (268113709 : ℕ)^263*25000000000000^199 ≤ 10970981746057^199*500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268113709 500000000 10970981746057 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2147895741/10000000000 : ℝ)^263 ≤ (13097345081653/100000000000000 : ℝ)^199 := by
    have hnat : (2147895741 : ℕ)^263*100000000000000^199 ≤ 13097345081653^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147895741 10000000000 13097345081653 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641043397/5000000000 : ℝ)^263 ≤ (43018727912757/100000000000000 : ℝ)^199 := by
    have hnat : (2641043397 : ℕ)^263*100000000000000^199 ≤ 43018727912757^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641043397 5000000000 43018727912757 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268113709/500000000 : ℝ), (-2147895741/10000000000 : ℝ), (2641043397/5000000000 : ℝ)] ![(10970981746057/25000000000000 : ℝ), (13097345081653/100000000000000 : ℝ), (43018727912757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268113709/500000000 : ℝ)|^263 ≤ (10970981746057/25000000000000 : ℝ)^199
        have hw : |(268113709/500000000 : ℝ)|=(268113709/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2147895741/10000000000 : ℝ)|^263 ≤ (13097345081653/100000000000000 : ℝ)^199
        have hw : |(-2147895741/10000000000 : ℝ)|=(2147895741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641043397/5000000000 : ℝ)|^263 ≤ (43018727912757/100000000000000 : ℝ)^199
        have hw : |(2641043397/5000000000 : ℝ)|=(2641043397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_box_6 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (83785529/156250000 : ℝ)*x 0 + (2641043511/5000000000 : ℝ)*x 1 + (-2147895873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83785529/156250000 : ℝ)^263 ≤ (1371372608747/3125000000000 : ℝ)^199 := by
    have hnat : (83785529 : ℕ)^263*3125000000000^199 ≤ 1371372608747^199*156250000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83785529 156250000 1371372608747 3125000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641043511/5000000000 : ℝ)^263 ≤ (21509365183421/50000000000000 : ℝ)^199 := by
    have hnat : (2641043511 : ℕ)^263*50000000000000^199 ≤ 21509365183421^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641043511 5000000000 21509365183421 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2147895873/10000000000 : ℝ)^263 ≤ (654867307271/5000000000000 : ℝ)^199 := by
    have hnat : (2147895873 : ℕ)^263*5000000000000^199 ≤ 654867307271^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147895873 10000000000 654867307271 5000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83785529/156250000 : ℝ), (2641043511/5000000000 : ℝ), (-2147895873/10000000000 : ℝ)] ![(1371372608747/3125000000000 : ℝ), (21509365183421/50000000000000 : ℝ), (654867307271/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83785529/156250000 : ℝ)|^263 ≤ (1371372608747/3125000000000 : ℝ)^199
        have hw : |(83785529/156250000 : ℝ)|=(83785529/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641043511/5000000000 : ℝ)|^263 ≤ (21509365183421/50000000000000 : ℝ)^199
        have hw : |(2641043511/5000000000 : ℝ)|=(2641043511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2147895873/10000000000 : ℝ)|^263 ≤ (654867307271/5000000000000 : ℝ)^199
        have hw : |(-2147895873/10000000000 : ℝ)|=(2147895873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_box_7 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (849255493/2000000000 : ℝ)*x 0 + (881795291/2000000000 : ℝ)*x 1 + (4408976403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849255493/2000000000 : ℝ)^263 ≤ (16119177357287/50000000000000 : ℝ)^199 := by
    have hnat : (849255493 : ℕ)^263*50000000000000^199 ≤ 16119177357287^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849255493 2000000000 16119177357287 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (881795291/2000000000 : ℝ)^263 ≤ (1355232915853/4000000000000 : ℝ)^199 := by
    have hnat : (881795291 : ℕ)^263*4000000000000^199 ≤ 1355232915853^199*2000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881795291 2000000000 1355232915853 4000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4408976403/10000000000 : ℝ)^263 ≤ (16940411184109/50000000000000 : ℝ)^199 := by
    have hnat : (4408976403 : ℕ)^263*50000000000000^199 ≤ 16940411184109^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4408976403 10000000000 16940411184109 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849255493/2000000000 : ℝ), (881795291/2000000000 : ℝ), (4408976403/10000000000 : ℝ)] ![(16119177357287/50000000000000 : ℝ), (1355232915853/4000000000000 : ℝ), (16940411184109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849255493/2000000000 : ℝ)|^263 ≤ (16119177357287/50000000000000 : ℝ)^199
        have hw : |(849255493/2000000000 : ℝ)|=(849255493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(881795291/2000000000 : ℝ)|^263 ≤ (1355232915853/4000000000000 : ℝ)^199
        have hw : |(881795291/2000000000 : ℝ)|=(881795291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4408976403/10000000000 : ℝ)|^263 ≤ (16940411184109/50000000000000 : ℝ)^199
        have hw : |(4408976403/10000000000 : ℝ)|=(4408976403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_box_8 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1101028129/5000000000 : ℝ)*x 0 + (5218657857/10000000000 : ℝ)*x 1 + (5384741543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101028129/5000000000 : ℝ)^263 ≤ (6767788020419/50000000000000 : ℝ)^199 := by
    have hnat : (1101028129 : ℕ)^263*50000000000000^199 ≤ 6767788020419^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101028129 5000000000 6767788020419 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218657857/10000000000 : ℝ)^263 ≤ (21168665300283/50000000000000 : ℝ)^199 := by
    have hnat : (5218657857 : ℕ)^263*50000000000000^199 ≤ 21168665300283^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218657857 10000000000 21168665300283 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384741543/10000000000 : ℝ)^263 ≤ (5515886666601/12500000000000 : ℝ)^199 := by
    have hnat : (5384741543 : ℕ)^263*12500000000000^199 ≤ 5515886666601^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384741543 10000000000 5515886666601 12500000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1101028129/5000000000 : ℝ), (5218657857/10000000000 : ℝ), (5384741543/10000000000 : ℝ)] ![(6767788020419/50000000000000 : ℝ), (21168665300283/50000000000000 : ℝ), (5515886666601/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1101028129/5000000000 : ℝ)|^263 ≤ (6767788020419/50000000000000 : ℝ)^199
        have hw : |(-1101028129/5000000000 : ℝ)|=(1101028129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218657857/10000000000 : ℝ)|^263 ≤ (21168665300283/50000000000000 : ℝ)^199
        have hw : |(5218657857/10000000000 : ℝ)|=(5218657857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384741543/10000000000 : ℝ)|^263 ≤ (5515886666601/12500000000000 : ℝ)^199
        have hw : |(5384741543/10000000000 : ℝ)|=(5384741543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_box_9 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2644938181/5000000000 : ℝ)*x 0 + (-2107191099/10000000000 : ℝ)*x 1 + (1346185361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644938181/5000000000 : ℝ)^263 ≤ (21551295516587/50000000000000 : ℝ)^199 := by
    have hnat : (2644938181 : ℕ)^263*50000000000000^199 ≤ 21551295516587^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644938181 5000000000 21551295516587 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107191099/10000000000 : ℝ)^263 ≤ (6385158342117/50000000000000 : ℝ)^199 := by
    have hnat : (2107191099 : ℕ)^263*50000000000000^199 ≤ 6385158342117^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107191099 10000000000 6385158342117 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346185361/2500000000 : ℝ)^263 ≤ (22063546130301/50000000000000 : ℝ)^199 := by
    have hnat : (1346185361 : ℕ)^263*50000000000000^199 ≤ 22063546130301^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346185361 2500000000 22063546130301 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644938181/5000000000 : ℝ), (-2107191099/10000000000 : ℝ), (1346185361/2500000000 : ℝ)] ![(21551295516587/50000000000000 : ℝ), (6385158342117/50000000000000 : ℝ), (22063546130301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644938181/5000000000 : ℝ)|^263 ≤ (21551295516587/50000000000000 : ℝ)^199
        have hw : |(2644938181/5000000000 : ℝ)|=(2644938181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2107191099/10000000000 : ℝ)|^263 ≤ (6385158342117/50000000000000 : ℝ)^199
        have hw : |(-2107191099/10000000000 : ℝ)|=(2107191099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346185361/2500000000 : ℝ)|^263 ≤ (22063546130301/50000000000000 : ℝ)^199
        have hw : |(1346185361/2500000000 : ℝ)|=(1346185361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_box_10 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2644938149/5000000000 : ℝ)*x 0 + (43077933/80000000 : ℝ)*x 1 + (-1053595471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644938149/5000000000 : ℝ)^263 ≤ (43102590343981/100000000000000 : ℝ)^199 := by
    have hnat : (2644938149 : ℕ)^263*100000000000000^199 ≤ 43102590343981^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644938149 5000000000 43102590343981 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43077933/80000000 : ℝ)^263 ≤ (22063547110449/50000000000000 : ℝ)^199 := by
    have hnat : (43077933 : ℕ)^263*50000000000000^199 ≤ 22063547110449^199*80000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43077933 80000000 22063547110449 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053595471/5000000000 : ℝ)^263 ≤ (12770315426757/100000000000000 : ℝ)^199 := by
    have hnat : (1053595471 : ℕ)^263*100000000000000^199 ≤ 12770315426757^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053595471 5000000000 12770315426757 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644938149/5000000000 : ℝ), (43077933/80000000 : ℝ), (-1053595471/5000000000 : ℝ)] ![(43102590343981/100000000000000 : ℝ), (22063547110449/50000000000000 : ℝ), (12770315426757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644938149/5000000000 : ℝ)|^263 ≤ (43102590343981/100000000000000 : ℝ)^199
        have hw : |(2644938149/5000000000 : ℝ)|=(2644938149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43077933/80000000 : ℝ)|^263 ≤ (22063547110449/50000000000000 : ℝ)^199
        have hw : |(43077933/80000000 : ℝ)|=(43077933/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1053595471/5000000000 : ℝ)|^263 ≤ (12770315426757/100000000000000 : ℝ)^199
        have hw : |(-1053595471/5000000000 : ℝ)|=(1053595471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_box_11 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1120480623/2500000000 : ℝ)*x 0 + (1072758391/2500000000 : ℝ)*x 1 + (4291033653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120480623/2500000000 : ℝ)^263 ≤ (17311809966913/50000000000000 : ℝ)^199 := by
    have hnat : (1120480623 : ℕ)^263*50000000000000^199 ≤ 17311809966913^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120480623 2500000000 17311809966913 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072758391/2500000000 : ℝ)^263 ≤ (6537637915669/20000000000000 : ℝ)^199 := by
    have hnat : (1072758391 : ℕ)^263*20000000000000^199 ≤ 6537637915669^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072758391 2500000000 6537637915669 20000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4291033653/10000000000 : ℝ)^263 ≤ (32688190474373/100000000000000 : ℝ)^199 := by
    have hnat : (4291033653 : ℕ)^263*100000000000000^199 ≤ 32688190474373^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291033653 10000000000 32688190474373 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120480623/2500000000 : ℝ), (1072758391/2500000000 : ℝ), (4291033653/10000000000 : ℝ)] ![(17311809966913/50000000000000 : ℝ), (6537637915669/20000000000000 : ℝ), (32688190474373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120480623/2500000000 : ℝ)|^263 ≤ (17311809966913/50000000000000 : ℝ)^199
        have hw : |(1120480623/2500000000 : ℝ)|=(1120480623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1072758391/2500000000 : ℝ)|^263 ≤ (6537637915669/20000000000000 : ℝ)^199
        have hw : |(1072758391/2500000000 : ℝ)|=(1072758391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4291033653/10000000000 : ℝ)|^263 ≤ (32688190474373/100000000000000 : ℝ)^199
        have hw : |(4291033653/10000000000 : ℝ)|=(4291033653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_box_12 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-41141683/200000000 : ℝ)*x 0 + (271866817/500000000 : ℝ)*x 1 + (5274014273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41141683/200000000 : ℝ)^263 ≤ (6185266300659/50000000000000 : ℝ)^199 := by
    have hnat : (41141683 : ℕ)^263*50000000000000^199 ≤ 6185266300659^199*200000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41141683 200000000 6185266300659 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271866817/500000000 : ℝ)^263 ≤ (11174401731959/25000000000000 : ℝ)^199 := by
    have hnat : (271866817 : ℕ)^263*25000000000000^199 ≤ 11174401731959^199*500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271866817 500000000 11174401731959 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274014273/10000000000 : ℝ)^263 ≤ (42931860456011/100000000000000 : ℝ)^199 := by
    have hnat : (5274014273 : ℕ)^263*100000000000000^199 ≤ 42931860456011^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274014273 10000000000 42931860456011 100000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41141683/200000000 : ℝ), (271866817/500000000 : ℝ), (5274014273/10000000000 : ℝ)] ![(6185266300659/50000000000000 : ℝ), (11174401731959/25000000000000 : ℝ), (42931860456011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41141683/200000000 : ℝ)|^263 ≤ (6185266300659/50000000000000 : ℝ)^199
        have hw : |(-41141683/200000000 : ℝ)|=(41141683/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271866817/500000000 : ℝ)|^263 ≤ (11174401731959/25000000000000 : ℝ)^199
        have hw : |(271866817/500000000 : ℝ)|=(271866817/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274014273/10000000000 : ℝ)|^263 ≤ (42931860456011/100000000000000 : ℝ)^199
        have hw : |(5274014273/10000000000 : ℝ)|=(5274014273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_box_13 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2683982397/5000000000 : ℝ)*x 0 + (-537758793/2500000000 : ℝ)*x 1 + (5274014479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683982397/5000000000 : ℝ)^263 ≤ (2197274304879/5000000000000 : ℝ)^199 := by
    have hnat : (2683982397 : ℕ)^263*5000000000000^199 ≤ 2197274304879^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683982397 5000000000 2197274304879 5000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537758793/2500000000 : ℝ)^263 ≤ (656132560531/5000000000000 : ℝ)^199 := by
    have hnat : (537758793 : ℕ)^263*5000000000000^199 ≤ 656132560531^199*2500000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537758793 2500000000 656132560531 5000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274014479/10000000000 : ℝ)^263 ≤ (2683241417013/6250000000000 : ℝ)^199 := by
    have hnat : (5274014479 : ℕ)^263*6250000000000^199 ≤ 2683241417013^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274014479 10000000000 2683241417013 6250000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683982397/5000000000 : ℝ), (-537758793/2500000000 : ℝ), (5274014479/10000000000 : ℝ)] ![(2197274304879/5000000000000 : ℝ), (656132560531/5000000000000 : ℝ), (2683241417013/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683982397/5000000000 : ℝ)|^263 ≤ (2197274304879/5000000000000 : ℝ)^199
        have hw : |(2683982397/5000000000 : ℝ)|=(2683982397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-537758793/2500000000 : ℝ)|^263 ≤ (656132560531/5000000000000 : ℝ)^199
        have hw : |(-537758793/2500000000 : ℝ)|=(537758793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274014479/10000000000 : ℝ)|^263 ≤ (2683241417013/6250000000000 : ℝ)^199
        have hw : |(5274014479/10000000000 : ℝ)|=(5274014479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_box_14 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (335497819/625000000 : ℝ)*x 0 + (2637007169/5000000000 : ℝ)*x 1 + (-33609921/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335497819/625000000 : ℝ)^263 ≤ (21972744725813/50000000000000 : ℝ)^199 := by
    have hnat : (335497819 : ℕ)^263*50000000000000^199 ≤ 21972744725813^199*625000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335497819 625000000 21972744725813 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2637007169/5000000000 : ℝ)^263 ≤ (1341620661103/3125000000000 : ℝ)^199 := by
    have hnat : (2637007169 : ℕ)^263*3125000000000^199 ≤ 1341620661103^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637007169 5000000000 1341620661103 3125000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33609921/156250000 : ℝ)^263 ≤ (656132468617/5000000000000 : ℝ)^199 := by
    have hnat : (33609921 : ℕ)^263*5000000000000^199 ≤ 656132468617^199*156250000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33609921 156250000 656132468617 5000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335497819/625000000 : ℝ), (2637007169/5000000000 : ℝ), (-33609921/156250000 : ℝ)] ![(21972744725813/50000000000000 : ℝ), (1341620661103/3125000000000 : ℝ), (656132468617/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335497819/625000000 : ℝ)|^263 ≤ (21972744725813/50000000000000 : ℝ)^199
        have hw : |(335497819/625000000 : ℝ)|=(335497819/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2637007169/5000000000 : ℝ)|^263 ≤ (1341620661103/3125000000000 : ℝ)^199
        have hw : |(2637007169/5000000000 : ℝ)|=(2637007169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33609921/156250000 : ℝ)|^263 ≤ (656132468617/5000000000000 : ℝ)^199
        have hw : |(-33609921/156250000 : ℝ)|=(33609921/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1223_box_15 (p : ℝ) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ)) (x : Fin 3 → ℝ) :
    (528436689/1250000000 : ℝ)*x 0 + (2209123027/5000000000 : ℝ)*x 1 + (4418245503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528436689/1250000000 : ℝ)^263 ≤ (8012503434717/25000000000000 : ℝ)^199 := by
    have hnat : (528436689 : ℕ)^263*25000000000000^199 ≤ 8012503434717^199*1250000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528436689 1250000000 8012503434717 25000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2209123027/5000000000 : ℝ)^263 ≤ (16987497960719/50000000000000 : ℝ)^199 := by
    have hnat : (2209123027 : ℕ)^263*50000000000000^199 ≤ 16987497960719^199*5000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209123027 5000000000 16987497960719 50000000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4418245503/10000000000 : ℝ)^263 ≤ (135899961287/400000000000 : ℝ)^199 := by
    have hnat : (4418245503 : ℕ)^263*400000000000^199 ≤ 135899961287^199*10000000000^263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418245503 10000000000 135899961287 400000000000 263 199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (263/64 : ℝ)) 263 199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528436689/1250000000 : ℝ), (2209123027/5000000000 : ℝ), (4418245503/10000000000 : ℝ)] ![(8012503434717/25000000000000 : ℝ), (16987497960719/50000000000000 : ℝ), (135899961287/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528436689/1250000000 : ℝ)|^263 ≤ (8012503434717/25000000000000 : ℝ)^199
        have hw : |(528436689/1250000000 : ℝ)|=(528436689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2209123027/5000000000 : ℝ)|^263 ≤ (16987497960719/50000000000000 : ℝ)^199
        have hw : |(2209123027/5000000000 : ℝ)|=(2209123027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4418245503/10000000000 : ℝ)|^263 ≤ (135899961287/400000000000 : ℝ)^199
        have hw : |(4418245503/10000000000 : ℝ)|=(4418245503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1223_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h) :
    -(62243/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29681/50000 : ℝ) ∧ (80053/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10413/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7047/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (358/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7047/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (358/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7047/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (358/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7047/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (358/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7047/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (358/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7047/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (358/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (358/3125 : ℝ) ^ (8415/2048 : ℝ) ≤ (3401051592038987/25000000000000000000 : ℝ) := by
    have hpowers : (358/3125 : ℝ)^8415 ≤ (3401051592038987/25000000000000000000 : ℝ)^2048 := by
      have hnat : (358 : ℕ)^8415*25000000000000000000^2048 ≤ 3401051592038987^2048*3125^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        358 3125 3401051592038987 25000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (358/3125 : ℝ)) (X := (3401051592038987/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7047/50000 : ℝ) ^ (8415/2048 : ℝ) ≤ (7969263942073889/25000000000000000000 : ℝ) := by
    have hpowers : (7047/50000 : ℝ)^8415 ≤ (7969263942073889/25000000000000000000 : ℝ)^2048 := by
      have hnat : (7047 : ℕ)^8415*25000000000000000000^2048 ≤ 7969263942073889^2048*50000^8415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7047 50000 7969263942073889 25000000000000000000 8415 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7047/50000 : ℝ)) (X := (7969263942073889/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503401051592038987/12500000000000000000 : ℝ) ≤ (2500165529098303/2500000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (12503401051592038987/12500000000000000000 : ℝ)^2048 ≤ (2500165529098303/2500000000000000 : ℝ)^8415 := by
      have hnat : (12503401051592038987 : ℕ)^2048*2500000000000000^8415 ≤ 2500165529098303^8415*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503401051592038987 12500000000000000000 2500165529098303 2500000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500165529098303/2500000000000000 : ℝ)) (X := (12503401051592038987/12500000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252842578883528219/6250000000000000000 : ℝ) ≤ (10001106709475501/10000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (6252842578883528219/6250000000000000000 : ℝ)^2048 ≤ (10001106709475501/10000000000000000 : ℝ)^8415 := by
      have hnat : (6252842578883528219 : ℕ)^2048*10000000000000000^8415 ≤ 10001106709475501^8415*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252842578883528219 6250000000000000000 10001106709475501 10000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001106709475501/10000000000000000 : ℝ)) (X := (6252842578883528219/6250000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507969263942073889/12500000000000000000 : ℝ) ≤ (1000155130255779/1000000000000000 : ℝ) ^ (8415/2048 : ℝ) := by
    have hpowers : (12507969263942073889/12500000000000000000 : ℝ)^2048 ≤ (1000155130255779/1000000000000000 : ℝ)^8415 := by
      have hnat : (12507969263942073889 : ℕ)^2048*1000000000000000^8415 ≤ 1000155130255779^8415*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507969263942073889 12500000000000000000 1000155130255779 1000000000000000 2048 8415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000155130255779/1000000000000000 : ℝ)) (X := (12507969263942073889/12500000000000000000 : ℝ)) (by norm_num) 8415 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3401051592038987/25000000000000000000 : ℝ) ≤ ((3296445018292985961/3297500000000000000 : ℝ)+2*(444593082289/263800000000000 : ℝ)*(358/3125 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (3296445018292985961/3297500000000000000 : ℝ)+2*(444593082289/263800000000000 : ℝ)*(358/3125 : ℝ)=(2500165529098303/2500000000000000 : ℝ) by norm_num, show 1+2*(3401051592038987/25000000000000000000 : ℝ)=(12503401051592038987/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7969263942073889/25000000000000000000 : ℝ)+(3401051592038987/25000000000000000000 : ℝ) ≤ ((3296445018292985961/3297500000000000000 : ℝ)+(444593082289/263800000000000 : ℝ)*((7047/50000 : ℝ)+(358/3125 : ℝ)))^(8415/2048 : ℝ) := by
    rw [show (3296445018292985961/3297500000000000000 : ℝ)+(444593082289/263800000000000 : ℝ)*((7047/50000 : ℝ)+(358/3125 : ℝ))=(10001106709475501/10000000000000000 : ℝ) by norm_num, show 1+(7969263942073889/25000000000000000000 : ℝ)+(3401051592038987/25000000000000000000 : ℝ)=(6252842578883528219/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7969263942073889/25000000000000000000 : ℝ) ≤ ((3296445018292985961/3297500000000000000 : ℝ)+2*(444593082289/263800000000000 : ℝ)*(7047/50000 : ℝ))^(8415/2048 : ℝ) := by
    rw [show (3296445018292985961/3297500000000000000 : ℝ)+2*(444593082289/263800000000000 : ℝ)*(7047/50000 : ℝ)=(1000155130255779/1000000000000000 : ℝ) by norm_num, show 1+2*(7969263942073889/25000000000000000000 : ℝ)=(12507969263942073889/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3296445018292985961/3297500000000000000 : ℝ)*(X 1 0+X 2 0)+(444593082289/263800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (358/3125 : ℝ)) (hi := (7047/50000 : ℝ)) (c := (3296445018292985961/3297500000000000000 : ℝ)) (alpha := (444593082289/263800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3296445018292985961/3297500000000000000 : ℝ)*(X 0 1+X 2 1)+(444593082289/263800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (358/3125 : ℝ)) (hi := (7047/50000 : ℝ)) (c := (3296445018292985961/3297500000000000000 : ℝ)) (alpha := (444593082289/263800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3296445018292985961/3297500000000000000 : ℝ)*(X 0 2+X 1 2)+(444593082289/263800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8415/2048 : ℝ)) (lo := (358/3125 : ℝ)) (hi := (7047/50000 : ℝ)) (c := (3296445018292985961/3297500000000000000 : ℝ)) (alpha := (444593082289/263800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2004454023/10000000000 : ℝ)*X 0 0+(537512853/1000000000 : ℝ)*X 0 1+(5375128619/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296658991/10000000000 : ℝ)*X 1 0+(-422212861/2000000000 : ℝ)*X 1 1+(2687564059/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((529665883/1000000000 : ℝ)*X 2 0+(1075025671/2000000000 : ℝ)*X 2 1+(-2111064201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1115025729/2500000000 : ℝ)*X 0 0+(2151041863/5000000000 : ℝ)*X 0 1+(4302084153/10000000000 : ℝ)*X 0 2+(1115025729/2500000000 : ℝ)*X 1 0+(2151041863/5000000000 : ℝ)*X 1 1+(4302084153/10000000000 : ℝ)*X 1 2+(1115025729/2500000000 : ℝ)*X 2 0+(2151041863/5000000000 : ℝ)*X 2 1+(4302084153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-563603859/2500000000 : ℝ)*X 0 0+(5282086883/10000000000 : ℝ)*X 0 1+(2641043493/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((268113709/500000000 : ℝ)*X 1 0+(-2147895741/10000000000 : ℝ)*X 1 1+(2641043397/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((83785529/156250000 : ℝ)*X 2 0+(2641043511/5000000000 : ℝ)*X 2 1+(-2147895873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((849255493/2000000000 : ℝ)*X 0 0+(881795291/2000000000 : ℝ)*X 0 1+(4408976403/10000000000 : ℝ)*X 0 2+(849255493/2000000000 : ℝ)*X 1 0+(881795291/2000000000 : ℝ)*X 1 1+(4408976403/10000000000 : ℝ)*X 1 2+(849255493/2000000000 : ℝ)*X 2 0+(881795291/2000000000 : ℝ)*X 2 1+(4408976403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1101028129/5000000000 : ℝ)*X 0 0+(5218657857/10000000000 : ℝ)*X 0 1+(5384741543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644938181/5000000000 : ℝ)*X 1 0+(-2107191099/10000000000 : ℝ)*X 1 1+(1346185361/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644938149/5000000000 : ℝ)*X 2 0+(43077933/80000000 : ℝ)*X 2 1+(-1053595471/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1120480623/2500000000 : ℝ)*X 0 0+(1072758391/2500000000 : ℝ)*X 0 1+(4291033653/10000000000 : ℝ)*X 0 2+(1120480623/2500000000 : ℝ)*X 1 0+(1072758391/2500000000 : ℝ)*X 1 1+(4291033653/10000000000 : ℝ)*X 1 2+(1120480623/2500000000 : ℝ)*X 2 0+(1072758391/2500000000 : ℝ)*X 2 1+(4291033653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-41141683/200000000 : ℝ)*X 0 0+(271866817/500000000 : ℝ)*X 0 1+(5274014273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2683982397/5000000000 : ℝ)*X 1 0+(-537758793/2500000000 : ℝ)*X 1 1+(5274014479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((335497819/625000000 : ℝ)*X 2 0+(2637007169/5000000000 : ℝ)*X 2 1+(-33609921/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((528436689/1250000000 : ℝ)*X 0 0+(2209123027/5000000000 : ℝ)*X 0 1+(4418245503/10000000000 : ℝ)*X 0 2+(528436689/1250000000 : ℝ)*X 1 0+(2209123027/5000000000 : ℝ)*X 1 1+(4418245503/10000000000 : ℝ)*X 1 2+(528436689/1250000000 : ℝ)*X 2 0+(2209123027/5000000000 : ℝ)*X 2 1+(4418245503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1223_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62243/100000 : ℝ) ≤ (-25654815198975986209083293068119/41218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53098127/50000000000000 : ℝ)*(upper1) + (32848789/20000000000000 : ℝ)*(lower4) + (16647179/100000000000000 : ℝ)*(upper5) + (1993744138345093/50000000000000 : ℝ)*(major0) + (1993744138345093/50000000000000 : ℝ)*(major1) + (1993744138345093/50000000000000 : ℝ)*(major2) + (4993909293/100000000000000 : ℝ)*(sp3) + (2677994382978987/50000000000000 : ℝ)*(sp4) + (5355984601944717/100000000000000 : ℝ)*(sp5) + (669496034884757/12500000000000 : ℝ)*(sp6) + (1319863574092093/50000000000000 : ℝ)*(sp7) + (2526460253/100000000000000 : ℝ)*(sp12) + (669047351/10000000000000 : ℝ)*(sp13) + (23013340171/100000000000000 : ℝ)*(sp14) + (65993303552337/2500000000000 : ℝ)*(f.failure) + (5355991292418227/100000000000000 : ℝ)*(f.sum) + (19538458433203/6595000000000000000000000000 : ℝ)*base66 + (698878215728048127/164875000000000000000000000000000 : ℝ)*base68 + (589874012973201873/164875000000000000000000000000000 : ℝ)*base69 + (1335922397735451873/164875000000000000000000000000000 : ℝ)*base71 + (5941417303767/1648750000000000000000000000 : ℝ)*base74 + (2121199847542576873/164875000000000000000000000000000 : ℝ)*base75 + (2118191171775451873/164875000000000000000000000000000 : ℝ)*base77 + (249019161047951873/164875000000000000000000000000000 : ℝ)*base79 + (8415013728813/1648750000000000000000000000 : ℝ)*base81 + (3105013/250000000000000000000 : ℝ)*base89 + (3105013/250000000000000000000 : ℝ)*base91 + (3105013/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29681/50000 : ℝ) ≤ (48938661791034254061908461687167/82437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112589009/100000000000000 : ℝ)*(upper0) + (3449209/50000000000000 : ℝ)*(lower3) + (111899/4000000000000 : ℝ)*(upper4) + (2026487088492349/50000000000000 : ℝ)*(major0) + (2026487088492349/50000000000000 : ℝ)*(major1) + (2026487088492349/50000000000000 : ℝ)*(major2) + (2701533324577599/50000000000000 : ℝ)*(sp0) + (2701450626696139/50000000000000 : ℝ)*(sp1) + (1080606726131629/20000000000000 : ℝ)*(sp2) + (1341541472102519/50000000000000 : ℝ)*(sp3) + (174860005691/100000000000000 : ℝ)*(sp9) + (2655171239/6250000000000 : ℝ)*(sp10) + (554315911/50000000000000 : ℝ)*(sp11) + (9464242771/100000000000000 : ℝ)*(sp12) + (134154202641843/5000000000000 : ℝ)*(f.failure) + (5403076113397969/100000000000000 : ℝ)*(f.sum) + (2220831327799/6595000000000000000000000000 : ℝ)*base66 + (807517911506825111/164875000000000000000000000000000 : ℝ)*base68 + (1378185719451799889/164875000000000000000000000000000 : ℝ)*base69 + (217001050272325111/164875000000000000000000000000000 : ℝ)*base72 + (18912674976677/3297500000000000000000000000 : ℝ)*base74 + (647468200127174889/164875000000000000000000000000000 : ℝ)*base75 + (48649539219575111/164875000000000000000000000000000 : ℝ)*base78 + (1191837974382450111/164875000000000000000000000000000 : ℝ)*base80 + (2410172586199/1648750000000000000000000000 : ℝ)*base81 + (3420193/500000000000000000000 : ℝ)*base90 + (3420193/500000000000000000000 : ℝ)*base92 + (3420193/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80053/100000 : ℝ) ≤ (131990692760359910219956061371449/164875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16504319/20000000000000 : ℝ)*(lower3) + (29132199/100000000000000 : ℝ)*(upper4) + (279/25000000000000 : ℝ)*(lower5) + (4520007436707201/100000000000000 : ℝ)*(major0) + (4520007436707201/100000000000000 : ℝ)*(major1) + (4520007436707201/100000000000000 : ℝ)*(major2) + (1450243091/50000000000000 : ℝ)*(sp0) + (26735009783/100000000000000 : ℝ)*(sp1) + (126502020071/100000000000000 : ℝ)*(sp2) + (3164186779/10000000000000 : ℝ)*(sp3) + (6021065154327803/100000000000000 : ℝ)*(sp8) + (3010520659902101/50000000000000 : ℝ)*(sp9) + (3010470776396957/50000000000000 : ℝ)*(sp10) + (748057543601383/25000000000000 : ℝ)*(sp11) + (1496130908136661/50000000000000 : ℝ)*(f.failure) + (1204213610962797/20000000000000 : ℝ)*(f.sum) + (80366613046529/13190000000000000000000000000 : ℝ)*base65 + (2720953726966032339/329750000000000000000000000000000 : ℝ)*base68 + (3744639761502532339/329750000000000000000000000000000 : ℝ)*base70 + (43763349015532339/329750000000000000000000000000000 : ℝ)*base72 + (32257172910839/13190000000000000000000000000 : ℝ)*base73 + (4122817966003782339/329750000000000000000000000000000 : ℝ)*base76 + (379661611959282339/329750000000000000000000000000000 : ℝ)*base78 + (1980735155680032339/329750000000000000000000000000000 : ℝ)*base80 + (17189858279241/13190000000000000000000000000 : ℝ)*base82 + (18957111/5000000000000000000000 : ℝ)*base90 + (18957111/5000000000000000000000 : ℝ)*base92 + (18957111/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-10413/12500 : ℝ) ≤ (-137343640744573551275666849240649/164875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16996191/50000000000000 : ℝ)*(lower0) + (59868707/25000000000000 : ℝ)*(lower2) + (8281089/5000000000000 : ℝ)*(upper3) + (18207299/12500000000000 : ℝ)*(upper5) + (4555391422424003/100000000000000 : ℝ)*(major0) + (4555391422424003/100000000000000 : ℝ)*(major1) + (4555391422424003/100000000000000 : ℝ)*(major2) + (3062084561/100000000000000 : ℝ)*(sp0) + (87277131711/100000000000000 : ℝ)*(sp5) + (73065384763/50000000000000 : ℝ)*(sp7) + (6122860861527271/100000000000000 : ℝ)*(sp12) + (153069416162003/2500000000000 : ℝ)*(sp13) + (6122863923611831/100000000000000 : ℝ)*(sp14) + (301554001629319/10000000000000 : ℝ)*(sp15) + (753921536765679/25000000000000 : ℝ)*(f.failure) + (6122863923611831/100000000000000 : ℝ)*(f.sum) + (31812135388363/13190000000000000000000000000 : ℝ)*base66 + (1019661486030740617/329750000000000000000000000000000 : ℝ)*base68 + (3051506373498240617/329750000000000000000000000000000 : ℝ)*base70 + (1518062834886759383/329750000000000000000000000000000 : ℝ)*base71 + (181789528732943/13190000000000000000000000000 : ℝ)*base74 + (2001750214684759383/329750000000000000000000000000000 : ℝ)*base75 + (227379072807759383/329750000000000000000000000000000 : ℝ)*base77 + (8929727179181259383/329750000000000000000000000000000 : ℝ)*base79 + (101611976755093/13190000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (16381771/2500000000000000000000 : ℝ)*base89 + (16381771/2500000000000000000000 : ℝ)*base91 + (16381771/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1223_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62243/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29681/50000 : ℝ) else (80053/100000 : ℝ) ≤ X j i ∧ X j i ≤ (10413/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1223_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1223_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62243/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29681/50000 : ℝ) else (80053/100000 : ℝ) ≤ X j i ∧ X j i ≤ (10413/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1223_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8415/2048 : ℝ) ≤ p) (hpb : p ≤ (263/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151056549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62243/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29681/50000 : ℝ) else (80053/100000 : ℝ) ≤ X j i ∧ X j i ≤ (10413/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1223_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

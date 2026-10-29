-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1365_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:19:28.296997+00:00
-- url     : https://prove2.me/submissions/3445bb4a-6f85-4bd0-a518-fb7d94fba4e6

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
theorem support_rectangle_w1365_s6_0 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2024262641/10000000000 : ℝ)*x 0 + (2705764447/5000000000 : ℝ)*x 1 + (5245281789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2024262641/10000000000 : ℝ)^4325 ≤ (2466576405917/20000000000000 : ℝ)^3301 := by
    have hnat : (2024262641 : ℕ)^4325*20000000000000^3301 ≤ 2466576405917^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024262641 10000000000 2466576405917 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705764447/5000000000 : ℝ)^4325 ≤ (44729437065209/100000000000000 : ℝ)^3301 := by
    have hnat : (2705764447 : ℕ)^4325*100000000000000^3301 ≤ 44729437065209^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705764447 5000000000 44729437065209 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245281789/10000000000 : ℝ)^4325 ≤ (21468840445647/50000000000000 : ℝ)^3301 := by
    have hnat : (5245281789 : ℕ)^4325*50000000000000^3301 ≤ 21468840445647^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245281789 10000000000 21468840445647 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2024262641/10000000000 : ℝ), (2705764447/5000000000 : ℝ), (5245281789/10000000000 : ℝ)] ![(2466576405917/20000000000000 : ℝ), (44729437065209/100000000000000 : ℝ), (21468840445647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2024262641/10000000000 : ℝ)|^4325 ≤ (2466576405917/20000000000000 : ℝ)^3301
        have hw : |(-2024262641/10000000000 : ℝ)|=(2024262641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705764447/5000000000 : ℝ)|^4325 ≤ (44729437065209/100000000000000 : ℝ)^3301
        have hw : |(2705764447/5000000000 : ℝ)|=(2705764447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245281789/10000000000 : ℝ)|^4325 ≤ (21468840445647/50000000000000 : ℝ)^3301
        have hw : |(5245281789/10000000000 : ℝ)|=(5245281789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s6_1 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348591649/10000000000 : ℝ)*x 0 + (-2108950063/10000000000 : ℝ)*x 1 + (5245281169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348591649/10000000000 : ℝ)^4325 ≤ (11012270537509/25000000000000 : ℝ)^3301 := by
    have hnat : (5348591649 : ℕ)^4325*25000000000000^3301 ≤ 11012270537509^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348591649 10000000000 11012270537509 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2108950063/10000000000 : ℝ)^4325 ≤ (3253310899101/25000000000000 : ℝ)^3301 := by
    have hnat : (2108950063 : ℕ)^4325*25000000000000^3301 ≤ 3253310899101^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108950063 10000000000 3253310899101 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245281169/10000000000 : ℝ)^4325 ≤ (21468837120797/50000000000000 : ℝ)^3301 := by
    have hnat : (5245281169 : ℕ)^4325*50000000000000^3301 ≤ 21468837120797^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245281169 10000000000 21468837120797 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348591649/10000000000 : ℝ), (-2108950063/10000000000 : ℝ), (5245281169/10000000000 : ℝ)] ![(11012270537509/25000000000000 : ℝ), (3253310899101/25000000000000 : ℝ), (21468837120797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348591649/10000000000 : ℝ)|^4325 ≤ (11012270537509/25000000000000 : ℝ)^3301
        have hw : |(5348591649/10000000000 : ℝ)|=(5348591649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2108950063/10000000000 : ℝ)|^4325 ≤ (3253310899101/25000000000000 : ℝ)^3301
        have hw : |(-2108950063/10000000000 : ℝ)|=(2108950063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245281169/10000000000 : ℝ)|^4325 ≤ (21468837120797/50000000000000 : ℝ)^3301
        have hw : |(5245281169/10000000000 : ℝ)|=(5245281169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s6_2 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348591621/10000000000 : ℝ)*x 0 + (1311320297/2500000000 : ℝ)*x 1 + (-84358003/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348591621/10000000000 : ℝ)^4325 ≤ (1376533807747/3125000000000 : ℝ)^3301 := by
    have hnat : (5348591621 : ℕ)^4325*3125000000000^3301 ≤ 1376533807747^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348591621 10000000000 1376533807747 3125000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311320297/2500000000 : ℝ)^4325 ≤ (670901163209/1562500000000 : ℝ)^3301 := by
    have hnat : (1311320297 : ℕ)^4325*1562500000000^3301 ≤ 670901163209^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311320297 2500000000 670901163209 1562500000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84358003/400000000 : ℝ)^4325 ≤ (13013243693419/100000000000000 : ℝ)^3301 := by
    have hnat : (84358003 : ℕ)^4325*100000000000000^3301 ≤ 13013243693419^3301*400000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84358003 400000000 13013243693419 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348591621/10000000000 : ℝ), (1311320297/2500000000 : ℝ), (-84358003/400000000 : ℝ)] ![(1376533807747/3125000000000 : ℝ), (670901163209/1562500000000 : ℝ), (13013243693419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348591621/10000000000 : ℝ)|^4325 ≤ (1376533807747/3125000000000 : ℝ)^3301
        have hw : |(5348591621/10000000000 : ℝ)|=(5348591621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311320297/2500000000 : ℝ)|^4325 ≤ (670901163209/1562500000000 : ℝ)^3301
        have hw : |(1311320297/2500000000 : ℝ)|=(1311320297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-84358003/400000000 : ℝ)|^4325 ≤ (13013243693419/100000000000000 : ℝ)^3301
        have hw : |(-84358003/400000000 : ℝ)|=(84358003/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s6_3 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4320640623/10000000000 : ℝ)*x 0 + (4148323299/10000000000 : ℝ)*x 1 + (4499559953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320640623/10000000000 : ℝ)^4325 ≤ (8325913558007/25000000000000 : ℝ)^3301 := by
    have hnat : (4320640623 : ℕ)^4325*25000000000000^3301 ≤ 8325913558007^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320640623 10000000000 8325913558007 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4148323299/10000000000 : ℝ)^4325 ≤ (15787131612463/50000000000000 : ℝ)^3301 := by
    have hnat : (4148323299 : ℕ)^4325*50000000000000^3301 ≤ 15787131612463^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148323299 10000000000 15787131612463 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499559953/10000000000 : ℝ)^4325 ≤ (548782539523/1562500000000 : ℝ)^3301 := by
    have hnat : (4499559953 : ℕ)^4325*1562500000000^3301 ≤ 548782539523^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499559953 10000000000 548782539523 1562500000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320640623/10000000000 : ℝ), (4148323299/10000000000 : ℝ), (4499559953/10000000000 : ℝ)] ![(8325913558007/25000000000000 : ℝ), (15787131612463/50000000000000 : ℝ), (548782539523/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320640623/10000000000 : ℝ)|^4325 ≤ (8325913558007/25000000000000 : ℝ)^3301
        have hw : |(4320640623/10000000000 : ℝ)|=(4320640623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4148323299/10000000000 : ℝ)|^4325 ≤ (15787131612463/50000000000000 : ℝ)^3301
        have hw : |(4148323299/10000000000 : ℝ)|=(4148323299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499559953/10000000000 : ℝ)|^4325 ≤ (548782539523/1562500000000 : ℝ)^3301
        have hw : |(4499559953/10000000000 : ℝ)|=(4499559953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s6_4 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-20242749/100000000 : ℝ)*x 0 + (2622938703/5000000000 : ℝ)*x 1 + (2705464979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20242749/100000000 : ℝ)^4325 ≤ (3083244971751/25000000000000 : ℝ)^3301 := by
    have hnat : (20242749 : ℕ)^4325*25000000000000^3301 ≤ 3083244971751^3301*100000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20242749 100000000 3083244971751 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622938703/5000000000 : ℝ)^4325 ≤ (21472034594013/50000000000000 : ℝ)^3301 := by
    have hnat : (2622938703 : ℕ)^4325*50000000000000^3301 ≤ 21472034594013^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622938703 5000000000 21472034594013 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705464979/5000000000 : ℝ)^4325 ≤ (44722950915023/100000000000000 : ℝ)^3301 := by
    have hnat : (2705464979 : ℕ)^4325*100000000000000^3301 ≤ 44722950915023^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705464979 5000000000 44722950915023 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-20242749/100000000 : ℝ), (2622938703/5000000000 : ℝ), (2705464979/5000000000 : ℝ)] ![(3083244971751/25000000000000 : ℝ), (21472034594013/50000000000000 : ℝ), (44722950915023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-20242749/100000000 : ℝ)|^4325 ≤ (3083244971751/25000000000000 : ℝ)^3301
        have hw : |(-20242749/100000000 : ℝ)|=(20242749/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622938703/5000000000 : ℝ)|^4325 ≤ (21472034594013/50000000000000 : ℝ)^3301
        have hw : |(2622938703/5000000000 : ℝ)|=(2622938703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705464979/5000000000 : ℝ)|^4325 ≤ (44722950915023/100000000000000 : ℝ)^3301
        have hw : |(2705464979/5000000000 : ℝ)|=(2705464979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s6_5 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326414637/2500000000 : ℝ)*x 0 + (-1943300869/10000000000 : ℝ)*x 1 + (2705465099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326414637/2500000000 : ℝ)^4325 ≤ (5448299270733/12500000000000 : ℝ)^3301 := by
    have hnat : (1326414637 : ℕ)^4325*12500000000000^3301 ≤ 5448299270733^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326414637 2500000000 5448299270733 12500000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1943300869/10000000000 : ℝ)^4325 ≤ (730665768753/6250000000000 : ℝ)^3301 := by
    have hnat : (1943300869 : ℕ)^4325*6250000000000^3301 ≤ 730665768753^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943300869 10000000000 730665768753 6250000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705465099/5000000000 : ℝ)^4325 ≤ (698796148657/1562500000000 : ℝ)^3301 := by
    have hnat : (2705465099 : ℕ)^4325*1562500000000^3301 ≤ 698796148657^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705465099 5000000000 698796148657 1562500000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326414637/2500000000 : ℝ), (-1943300869/10000000000 : ℝ), (2705465099/5000000000 : ℝ)] ![(5448299270733/12500000000000 : ℝ), (730665768753/6250000000000 : ℝ), (698796148657/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326414637/2500000000 : ℝ)|^4325 ≤ (5448299270733/12500000000000 : ℝ)^3301
        have hw : |(1326414637/2500000000 : ℝ)|=(1326414637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1943300869/10000000000 : ℝ)|^4325 ≤ (730665768753/6250000000000 : ℝ)^3301
        have hw : |(-1943300869/10000000000 : ℝ)|=(1943300869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705465099/5000000000 : ℝ)|^4325 ≤ (698796148657/1562500000000 : ℝ)^3301
        have hw : |(2705465099/5000000000 : ℝ)|=(2705465099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s6_6 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663207333/1250000000 : ℝ)*x 0 + (338183133/625000000 : ℝ)*x 1 + (-1943300807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663207333/1250000000 : ℝ)^4325 ≤ (21793197707213/50000000000000 : ℝ)^3301 := by
    have hnat : (663207333 : ℕ)^4325*50000000000000^3301 ≤ 21793197707213^3301*1250000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663207333 1250000000 21793197707213 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338183133/625000000 : ℝ)^4325 ≤ (44722952755999/100000000000000 : ℝ)^3301 := by
    have hnat : (338183133 : ℕ)^4325*100000000000000^3301 ≤ 44722952755999^3301*625000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338183133 625000000 44722952755999 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1943300807/10000000000 : ℝ)^4325 ≤ (11690651811361/100000000000000 : ℝ)^3301 := by
    have hnat : (1943300807 : ℕ)^4325*100000000000000^3301 ≤ 11690651811361^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943300807 10000000000 11690651811361 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663207333/1250000000 : ℝ), (338183133/625000000 : ℝ), (-1943300807/10000000000 : ℝ)] ![(21793197707213/50000000000000 : ℝ), (44722952755999/100000000000000 : ℝ), (11690651811361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663207333/1250000000 : ℝ)|^4325 ≤ (21793197707213/50000000000000 : ℝ)^3301
        have hw : |(663207333/1250000000 : ℝ)|=(663207333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338183133/625000000 : ℝ)|^4325 ≤ (44722952755999/100000000000000 : ℝ)^3301
        have hw : |(338183133/625000000 : ℝ)|=(338183133/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1943300807/10000000000 : ℝ)|^4325 ≤ (11690651811361/100000000000000 : ℝ)^3301
        have hw : |(-1943300807/10000000000 : ℝ)|=(1943300807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s6_7 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2160332649/5000000000 : ℝ)*x 0 + (899659913/2000000000 : ℝ)*x 1 + (4149590763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160332649/5000000000 : ℝ)^4325 ≤ (33303903428493/100000000000000 : ℝ)^3301 := by
    have hnat : (2160332649 : ℕ)^4325*100000000000000^3301 ≤ 33303903428493^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160332649 5000000000 33303903428493 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899659913/2000000000 : ℝ)^4325 ≤ (35109193025847/100000000000000 : ℝ)^3301 := by
    have hnat : (899659913 : ℕ)^4325*100000000000000^3301 ≤ 35109193025847^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899659913 2000000000 35109193025847 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4149590763/10000000000 : ℝ)^4325 ≤ (15793451763157/50000000000000 : ℝ)^3301 := by
    have hnat : (4149590763 : ℕ)^4325*50000000000000^3301 ≤ 15793451763157^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149590763 10000000000 15793451763157 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160332649/5000000000 : ℝ), (899659913/2000000000 : ℝ), (4149590763/10000000000 : ℝ)] ![(33303903428493/100000000000000 : ℝ), (35109193025847/100000000000000 : ℝ), (15793451763157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160332649/5000000000 : ℝ)|^4325 ≤ (33303903428493/100000000000000 : ℝ)^3301
        have hw : |(2160332649/5000000000 : ℝ)|=(2160332649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899659913/2000000000 : ℝ)|^4325 ≤ (35109193025847/100000000000000 : ℝ)^3301
        have hw : |(899659913/2000000000 : ℝ)|=(899659913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4149590763/10000000000 : ℝ)|^4325 ≤ (15793451763157/50000000000000 : ℝ)^3301
        have hw : |(4149590763/10000000000 : ℝ)|=(4149590763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1365_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2799/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5601/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7361/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1841/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2799/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1841/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2799/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1841/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2799/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1841/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2799/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1841/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2799/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1841/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2799/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2799/25000 : ℝ) ^ (1081/256 : ℝ) ≤ (482491284180891/5000000000000000000 : ℝ) := by
    have hpowers : (2799/25000 : ℝ)^1081 ≤ (482491284180891/5000000000000000000 : ℝ)^256 := by
      have hnat : (2799 : ℕ)^1081*5000000000000000000^256 ≤ 482491284180891^256*25000^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2799 25000 482491284180891 5000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2799/25000 : ℝ)) (X := (482491284180891/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1841/12500 : ℝ) ^ (1081/256 : ℝ) ≤ (30715466416425787/100000000000000000000 : ℝ) := by
    have hpowers : (1841/12500 : ℝ)^1081 ≤ (30715466416425787/100000000000000000000 : ℝ)^256 := by
      have hnat : (1841 : ℕ)^1081*100000000000000000000^256 ≤ 30715466416425787^256*12500^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1841 12500 30715466416425787 100000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1841/12500 : ℝ)) (X := (30715466416425787/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500482491284180891/2500000000000000000 : ℝ) ≤ (625028563522947/625000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (2500482491284180891/2500000000000000000 : ℝ)^256 ≤ (625028563522947/625000000000000 : ℝ)^1081 := by
      have hnat : (2500482491284180891 : ℕ)^256*625000000000000^1081 ≤ 625028563522947^1081*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500482491284180891 2500000000000000000 625028563522947 625000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625028563522947/625000000000000 : ℝ)) (X := (2500482491284180891/2500000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040365292100043607/100000000000000000000 : ℝ) ≤ (10000955774604997/10000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (100040365292100043607/100000000000000000000 : ℝ)^256 ≤ (10000955774604997/10000000000000000 : ℝ)^1081 := by
      have hnat : (100040365292100043607 : ℕ)^256*10000000000000000^1081 ≤ 10000955774604997^1081*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040365292100043607 100000000000000000000 10000955774604997 10000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000955774604997/10000000000000000 : ℝ)) (X := (100040365292100043607/100000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030715466416425787/50000000000000000000 : ℝ) ≤ (5000727266421421/5000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (50030715466416425787/50000000000000000000 : ℝ)^256 ≤ (5000727266421421/5000000000000000 : ℝ)^1081 := by
      have hnat : (50030715466416425787 : ℕ)^256*5000000000000000^1081 ≤ 5000727266421421^1081*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030715466416425787 50000000000000000000 5000727266421421 5000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000727266421421/5000000000000000 : ℝ)) (X := (50030715466416425787/50000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(482491284180891/5000000000000000000 : ℝ) ≤ ((4413805748418369453/4415000000000000000 : ℝ)+2*(99751647569/70640000000000 : ℝ)*(2799/25000 : ℝ))^(1081/256 : ℝ) := by
    rw [show (4413805748418369453/4415000000000000000 : ℝ)+2*(99751647569/70640000000000 : ℝ)*(2799/25000 : ℝ)=(625028563522947/625000000000000 : ℝ) by norm_num, show 1+2*(482491284180891/5000000000000000000 : ℝ)=(2500482491284180891/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30715466416425787/100000000000000000000 : ℝ)+(482491284180891/5000000000000000000 : ℝ) ≤ ((4413805748418369453/4415000000000000000 : ℝ)+(99751647569/70640000000000 : ℝ)*((1841/12500 : ℝ)+(2799/25000 : ℝ)))^(1081/256 : ℝ) := by
    rw [show (4413805748418369453/4415000000000000000 : ℝ)+(99751647569/70640000000000 : ℝ)*((1841/12500 : ℝ)+(2799/25000 : ℝ))=(10000955774604997/10000000000000000 : ℝ) by norm_num, show 1+(30715466416425787/100000000000000000000 : ℝ)+(482491284180891/5000000000000000000 : ℝ)=(100040365292100043607/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30715466416425787/100000000000000000000 : ℝ) ≤ ((4413805748418369453/4415000000000000000 : ℝ)+2*(99751647569/70640000000000 : ℝ)*(1841/12500 : ℝ))^(1081/256 : ℝ) := by
    rw [show (4413805748418369453/4415000000000000000 : ℝ)+2*(99751647569/70640000000000 : ℝ)*(1841/12500 : ℝ)=(5000727266421421/5000000000000000 : ℝ) by norm_num, show 1+2*(30715466416425787/100000000000000000000 : ℝ)=(50030715466416425787/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4413805748418369453/4415000000000000000 : ℝ)*(X 1 0+X 2 0)+(99751647569/70640000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (2799/25000 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (4413805748418369453/4415000000000000000 : ℝ)) (alpha := (99751647569/70640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4413805748418369453/4415000000000000000 : ℝ)*(X 0 1+X 2 1)+(99751647569/70640000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (2799/25000 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (4413805748418369453/4415000000000000000 : ℝ)) (alpha := (99751647569/70640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4413805748418369453/4415000000000000000 : ℝ)*(X 0 2+X 1 2)+(99751647569/70640000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (2799/25000 : ℝ)) (hi := (1841/12500 : ℝ)) (c := (4413805748418369453/4415000000000000000 : ℝ)) (alpha := (99751647569/70640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2024262641/10000000000 : ℝ)*X 0 0+(2705764447/5000000000 : ℝ)*X 0 1+(5245281789/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348591649/10000000000 : ℝ)*X 1 0+(-2108950063/10000000000 : ℝ)*X 1 1+(5245281169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348591621/10000000000 : ℝ)*X 2 0+(1311320297/2500000000 : ℝ)*X 2 1+(-84358003/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320640623/10000000000 : ℝ)*X 0 0+(4148323299/10000000000 : ℝ)*X 0 1+(4499559953/10000000000 : ℝ)*X 0 2+(4320640623/10000000000 : ℝ)*X 1 0+(4148323299/10000000000 : ℝ)*X 1 1+(4499559953/10000000000 : ℝ)*X 1 2+(4320640623/10000000000 : ℝ)*X 2 0+(4148323299/10000000000 : ℝ)*X 2 1+(4499559953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-20242749/100000000 : ℝ)*X 0 0+(2622938703/5000000000 : ℝ)*X 0 1+(2705464979/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326414637/2500000000 : ℝ)*X 1 0+(-1943300869/10000000000 : ℝ)*X 1 1+(2705465099/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663207333/1250000000 : ℝ)*X 2 0+(338183133/625000000 : ℝ)*X 2 1+(-1943300807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2160332649/5000000000 : ℝ)*X 0 0+(899659913/2000000000 : ℝ)*X 0 1+(4149590763/10000000000 : ℝ)*X 0 2+(2160332649/5000000000 : ℝ)*X 1 0+(899659913/2000000000 : ℝ)*X 1 1+(4149590763/10000000000 : ℝ)*X 1 2+(2160332649/5000000000 : ℝ)*X 2 0+(899659913/2000000000 : ℝ)*X 2 1+(4149590763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (339733549849717192940601141/55187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63926839/12500000000000 : ℝ)*(base19) + (282330501/100000000000000 : ℝ)*(lower2) + (44282919/50000000000000 : ℝ)*(lower4) + (7527843/4000000000000 : ℝ)*(upper5) + (1107780694295499/25000000000000 : ℝ)*(major0) + (1107780694295499/25000000000000 : ℝ)*(major1) + (1107780694295499/25000000000000 : ℝ)*(major2) + (6015131683956469/100000000000000 : ℝ)*(sp0) + (6015123338216081/100000000000000 : ℝ)*(sp1) + (15037772980941/250000000000 : ℝ)*(sp2) + (1423549637329789/50000000000000 : ℝ)*(sp3) + (1958581419/25000000000000 : ℝ)*(sp5) + (22491580069/100000000000000 : ℝ)*(sp6) + (7195274177/50000000000000 : ℝ)*(sp7) + (711778416301983/25000000000000 : ℝ)*(f.failure) + (6015131683956469/100000000000000 : ℝ)*(f.sum) + (6901068239/8830000000000000000000000 : ℝ)*base65 + (544415704266570453/110375000000000000000000000000000 : ℝ)*base68 + (174360101703695453/110375000000000000000000000000000 : ℝ)*base70 + (3616058520173445453/110375000000000000000000000000000 : ℝ)*base72 + (209277976569/220750000000000000000000000 : ℝ)*base73 + (4390418828925304547/110375000000000000000000000000000 : ℝ)*base75 + (3194241274388070453/110375000000000000000000000000000 : ℝ)*base78 + (3056031503643679547/110375000000000000000000000000000 : ℝ)*base79 + (243411833867/220750000000000000000000000 : ℝ)*base82 + (254649/625000000000000000000 : ℝ)*base89 + (254649/625000000000000000000 : ℝ)*base91 + (254649/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2313922471860395007317303013/220750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (98515163/6250000000000 : ℝ)*(base19) + (465360433/25000000000000 : ℝ)*(base23) + (22628481/10000000000000 : ℝ)*(upper3) + (51214391/100000000000000 : ℝ)*(lower4) + (162480031/100000000000000 : ℝ)*(upper5) + (4463198980014493/100000000000000 : ℝ)*(major0) + (4463198980014493/100000000000000 : ℝ)*(major1) + (4463198980014493/100000000000000 : ℝ)*(major2) + (3878514163/10000000000000 : ℝ)*(sp1) + (1429107297/3125000000000 : ℝ)*(sp2) + (1211734827224037/20000000000000 : ℝ)*(sp4) + (6058633774735947/100000000000000 : ℝ)*(sp5) + (6058626543244949/100000000000000 : ℝ)*(sp6) + (358465434313203/12500000000000 : ℝ)*(sp7) + (358465434313203/12500000000000 : ℝ)*(f.failure) + (1211734827224037/20000000000000 : ℝ)*(f.sum) + (10816819193053/3532000000000000000000000000 : ℝ)*base65 + (802140943658294829/441500000000000000000000000000000 : ℝ)*base67 + (1287587998470294829/441500000000000000000000000000000 : ℝ)*base69 + (4766505226523705171/441500000000000000000000000000000 : ℝ)*base72 + (33836934799353/3532000000000000000000000000 : ℝ)*base73 + (3481670484111294829/441500000000000000000000000000000 : ℝ)*base75 + (87573016175294829/441500000000000000000000000000000 : ℝ)*base77 + (4160321755672705171/441500000000000000000000000000000 : ℝ)*base80 + (3789958113009/3532000000000000000000000000 : ℝ)*base81 + (3478691/312500000000000000000 : ℝ)*base90 + (3478691/312500000000000000000 : ℝ)*base92 + (3478691/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1365_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2799/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1365_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1365_s7_0 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2024267533/10000000000 : ℝ)*x 0 + (5411481709/10000000000 : ℝ)*x 1 + (163916431/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2024267533/10000000000 : ℝ)^4325 ≤ (12332921079933/100000000000000 : ℝ)^3301 := by
    have hnat : (2024267533 : ℕ)^4325*100000000000000^3301 ≤ 12332921079933^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024267533 10000000000 12332921079933 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411481709/10000000000 : ℝ)^4325 ≤ (11182231517329/25000000000000 : ℝ)^3301 := by
    have hnat : (5411481709 : ℕ)^4325*25000000000000^3301 ≤ 11182231517329^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411481709 10000000000 11182231517329 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163916431/312500000 : ℝ)^4325 ≤ (2146907641913/5000000000000 : ℝ)^3301 := by
    have hnat : (163916431 : ℕ)^4325*5000000000000^3301 ≤ 2146907641913^3301*312500000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163916431 312500000 2146907641913 5000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2024267533/10000000000 : ℝ), (5411481709/10000000000 : ℝ), (163916431/312500000 : ℝ)] ![(12332921079933/100000000000000 : ℝ), (11182231517329/25000000000000 : ℝ), (2146907641913/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2024267533/10000000000 : ℝ)|^4325 ≤ (12332921079933/100000000000000 : ℝ)^3301
        have hw : |(-2024267533/10000000000 : ℝ)|=(2024267533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411481709/10000000000 : ℝ)|^4325 ≤ (11182231517329/25000000000000 : ℝ)^3301
        have hw : |(5411481709/10000000000 : ℝ)|=(5411481709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163916431/312500000 : ℝ)|^4325 ≤ (2146907641913/5000000000000 : ℝ)^3301
        have hw : |(163916431/312500000 : ℝ)|=(163916431/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s7_1 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348579893/10000000000 : ℝ)*x 0 + (-421781319/2000000000 : ℝ)*x 1 + (5245325761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348579893/10000000000 : ℝ)^4325 ≤ (44048955298001/100000000000000 : ℝ)^3301 := by
    have hnat : (5348579893 : ℕ)^4325*100000000000000^3301 ≤ 44048955298001^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348579893 10000000000 44048955298001 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421781319/2000000000 : ℝ)^4325 ≤ (406652880471/3125000000000 : ℝ)^3301 := by
    have hnat : (421781319 : ℕ)^4325*3125000000000^3301 ≤ 406652880471^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421781319 2000000000 406652880471 3125000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245325761/10000000000 : ℝ)^4325 ≤ (21469076252887/50000000000000 : ℝ)^3301 := by
    have hnat : (5245325761 : ℕ)^4325*50000000000000^3301 ≤ 21469076252887^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245325761 10000000000 21469076252887 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348579893/10000000000 : ℝ), (-421781319/2000000000 : ℝ), (5245325761/10000000000 : ℝ)] ![(44048955298001/100000000000000 : ℝ), (406652880471/3125000000000 : ℝ), (21469076252887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348579893/10000000000 : ℝ)|^4325 ≤ (44048955298001/100000000000000 : ℝ)^3301
        have hw : |(5348579893/10000000000 : ℝ)|=(5348579893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-421781319/2000000000 : ℝ)|^4325 ≤ (406652880471/3125000000000 : ℝ)^3301
        have hw : |(-421781319/2000000000 : ℝ)|=(421781319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245325761/10000000000 : ℝ)|^4325 ≤ (21469076252887/50000000000000 : ℝ)^3301
        have hw : |(5245325761/10000000000 : ℝ)|=(5245325761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s7_2 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674289941/5000000000 : ℝ)*x 0 + (5245325767/10000000000 : ℝ)*x 1 + (-1054453301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674289941/5000000000 : ℝ)^4325 ≤ (44048955179307/100000000000000 : ℝ)^3301 := by
    have hnat : (2674289941 : ℕ)^4325*100000000000000^3301 ≤ 44048955179307^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674289941 5000000000 44048955179307 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245325767/10000000000 : ℝ)^4325 ≤ (21469076285063/50000000000000 : ℝ)^3301 := by
    have hnat : (5245325767 : ℕ)^4325*50000000000000^3301 ≤ 21469076285063^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245325767 10000000000 21469076285063 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054453301/5000000000 : ℝ)^4325 ≤ (813305764479/6250000000000 : ℝ)^3301 := by
    have hnat : (1054453301 : ℕ)^4325*6250000000000^3301 ≤ 813305764479^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054453301 5000000000 813305764479 6250000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674289941/5000000000 : ℝ), (5245325767/10000000000 : ℝ), (-1054453301/5000000000 : ℝ)] ![(44048955179307/100000000000000 : ℝ), (21469076285063/50000000000000 : ℝ), (813305764479/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674289941/5000000000 : ℝ)|^4325 ≤ (44048955179307/100000000000000 : ℝ)^3301
        have hw : |(2674289941/5000000000 : ℝ)|=(2674289941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245325767/10000000000 : ℝ)|^4325 ≤ (21469076285063/50000000000000 : ℝ)^3301
        have hw : |(5245325767/10000000000 : ℝ)|=(5245325767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1054453301/5000000000 : ℝ)|^4325 ≤ (813305764479/6250000000000 : ℝ)^3301
        have hw : |(-1054453301/5000000000 : ℝ)|=(1054453301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s7_3 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4320643491/10000000000 : ℝ)*x 0 + (103710539/250000000 : ℝ)*x 1 + (2249730653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320643491/10000000000 : ℝ)^4325 ≤ (832592079909/2500000000000 : ℝ)^3301 := by
    have hnat : (4320643491 : ℕ)^4325*2500000000000^3301 ≤ 832592079909^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320643491 10000000000 832592079909 2500000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103710539/250000000 : ℝ)^4325 ≤ (1973452695623/6250000000000 : ℝ)^3301 := by
    have hnat : (103710539 : ℕ)^4325*6250000000000^3301 ≤ 1973452695623^3301*250000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103710539 250000000 1973452695623 6250000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249730653/5000000000 : ℝ)^4325 ≤ (8780268416029/25000000000000 : ℝ)^3301 := by
    have hnat : (2249730653 : ℕ)^4325*25000000000000^3301 ≤ 8780268416029^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249730653 5000000000 8780268416029 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320643491/10000000000 : ℝ), (103710539/250000000 : ℝ), (2249730653/5000000000 : ℝ)] ![(832592079909/2500000000000 : ℝ), (1973452695623/6250000000000 : ℝ), (8780268416029/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320643491/10000000000 : ℝ)|^4325 ≤ (832592079909/2500000000000 : ℝ)^3301
        have hw : |(4320643491/10000000000 : ℝ)|=(4320643491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103710539/250000000 : ℝ)|^4325 ≤ (1973452695623/6250000000000 : ℝ)^3301
        have hw : |(103710539/250000000 : ℝ)|=(103710539/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249730653/5000000000 : ℝ)|^4325 ≤ (8780268416029/25000000000000 : ℝ)^3301
        have hw : |(2249730653/5000000000 : ℝ)|=(2249730653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s7_4 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-404855903/2000000000 : ℝ)*x 0 + (2622960733/5000000000 : ℝ)*x 1 + (5410882917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404855903/2000000000 : ℝ)^4325 ≤ (12333016726271/100000000000000 : ℝ)^3301 := by
    have hnat : (404855903 : ℕ)^4325*100000000000000^3301 ≤ 12333016726271^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404855903 2000000000 12333016726271 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622960733/5000000000 : ℝ)^4325 ≤ (21472270881491/50000000000000 : ℝ)^3301 := by
    have hnat : (2622960733 : ℕ)^4325*50000000000000^3301 ≤ 21472270881491^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622960733 5000000000 21472270881491 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410882917/10000000000 : ℝ)^4325 ≤ (8944488299217/20000000000000 : ℝ)^3301 := by
    have hnat : (5410882917 : ℕ)^4325*20000000000000^3301 ≤ 8944488299217^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410882917 10000000000 8944488299217 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-404855903/2000000000 : ℝ), (2622960733/5000000000 : ℝ), (5410882917/10000000000 : ℝ)] ![(12333016726271/100000000000000 : ℝ), (21472270881491/50000000000000 : ℝ), (8944488299217/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-404855903/2000000000 : ℝ)|^4325 ≤ (12333016726271/100000000000000 : ℝ)^3301
        have hw : |(-404855903/2000000000 : ℝ)|=(404855903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622960733/5000000000 : ℝ)|^4325 ≤ (21472270881491/50000000000000 : ℝ)^3301
        have hw : |(2622960733/5000000000 : ℝ)|=(2622960733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410882917/10000000000 : ℝ)|^4325 ≤ (8944488299217/20000000000000 : ℝ)^3301
        have hw : |(5410882917/10000000000 : ℝ)|=(5410882917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s7_5 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326417633/2500000000 : ℝ)*x 0 + (-971674717/5000000000 : ℝ)*x 1 + (5410882939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326417633/2500000000 : ℝ)^4325 ≤ (2724157697207/6250000000000 : ℝ)^3301 := by
    have hnat : (1326417633 : ℕ)^4325*6250000000000^3301 ≤ 2724157697207^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326417633 2500000000 2724157697207 6250000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (971674717/5000000000 : ℝ)^4325 ≤ (11691035093379/100000000000000 : ℝ)^3301 := by
    have hnat : (971674717 : ℕ)^4325*100000000000000^3301 ≤ 11691035093379^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971674717 5000000000 11691035093379 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410882939/10000000000 : ℝ)^4325 ≤ (5590305216791/12500000000000 : ℝ)^3301 := by
    have hnat : (5410882939 : ℕ)^4325*12500000000000^3301 ≤ 5590305216791^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410882939 10000000000 5590305216791 12500000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326417633/2500000000 : ℝ), (-971674717/5000000000 : ℝ), (5410882939/10000000000 : ℝ)] ![(2724157697207/6250000000000 : ℝ), (11691035093379/100000000000000 : ℝ), (5590305216791/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326417633/2500000000 : ℝ)|^4325 ≤ (2724157697207/6250000000000 : ℝ)^3301
        have hw : |(1326417633/2500000000 : ℝ)|=(1326417633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-971674717/5000000000 : ℝ)|^4325 ≤ (11691035093379/100000000000000 : ℝ)^3301
        have hw : |(-971674717/5000000000 : ℝ)|=(971674717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410882939/10000000000 : ℝ)|^4325 ≤ (5590305216791/12500000000000 : ℝ)^3301
        have hw : |(5410882939/10000000000 : ℝ)|=(5410882939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s7_6 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305670537/10000000000 : ℝ)*x 0 + (2705441479/5000000000 : ℝ)*x 1 + (-971674701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305670537/10000000000 : ℝ)^4325 ≤ (4358652320913/10000000000000 : ℝ)^3301 := by
    have hnat : (5305670537 : ℕ)^4325*10000000000000^3301 ≤ 4358652320913^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305670537 10000000000 4358652320913 10000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705441479/5000000000 : ℝ)^4325 ≤ (44722441940083/100000000000000 : ℝ)^3301 := by
    have hnat : (2705441479 : ℕ)^4325*100000000000000^3301 ≤ 44722441940083^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705441479 5000000000 44722441940083 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (971674701/5000000000 : ℝ)^4325 ≤ (182672419393/1562500000000 : ℝ)^3301 := by
    have hnat : (971674701 : ℕ)^4325*1562500000000^3301 ≤ 182672419393^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971674701 5000000000 182672419393 1562500000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305670537/10000000000 : ℝ), (2705441479/5000000000 : ℝ), (-971674701/5000000000 : ℝ)] ![(4358652320913/10000000000000 : ℝ), (44722441940083/100000000000000 : ℝ), (182672419393/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305670537/10000000000 : ℝ)|^4325 ≤ (4358652320913/10000000000000 : ℝ)^3301
        have hw : |(5305670537/10000000000 : ℝ)|=(5305670537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705441479/5000000000 : ℝ)|^4325 ≤ (44722441940083/100000000000000 : ℝ)^3301
        have hw : |(2705441479/5000000000 : ℝ)|=(2705441479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-971674701/5000000000 : ℝ)|^4325 ≤ (182672419393/1562500000000 : ℝ)^3301
        have hw : |(-971674701/5000000000 : ℝ)|=(971674701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_s7_7 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080167147/2500000000 : ℝ)*x 0 + (4498202789/10000000000 : ℝ)*x 1 + (4149686661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080167147/2500000000 : ℝ)^4325 ≤ (16651968327361/50000000000000 : ℝ)^3301 := by
    have hnat : (1080167147 : ℕ)^4325*50000000000000^3301 ≤ 16651968327361^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080167147 2500000000 16651968327361 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498202789/10000000000 : ℝ)^4325 ≤ (35108203381201/100000000000000 : ℝ)^3301 := by
    have hnat : (4498202789 : ℕ)^4325*100000000000000^3301 ≤ 35108203381201^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498202789 10000000000 35108203381201 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4149686661/10000000000 : ℝ)^4325 ≤ (3948482494619/12500000000000 : ℝ)^3301 := by
    have hnat : (4149686661 : ℕ)^4325*12500000000000^3301 ≤ 3948482494619^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149686661 10000000000 3948482494619 12500000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080167147/2500000000 : ℝ), (4498202789/10000000000 : ℝ), (4149686661/10000000000 : ℝ)] ![(16651968327361/50000000000000 : ℝ), (35108203381201/100000000000000 : ℝ), (3948482494619/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080167147/2500000000 : ℝ)|^4325 ≤ (16651968327361/50000000000000 : ℝ)^3301
        have hw : |(1080167147/2500000000 : ℝ)|=(1080167147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498202789/10000000000 : ℝ)|^4325 ≤ (35108203381201/100000000000000 : ℝ)^3301
        have hw : |(4498202789/10000000000 : ℝ)|=(4498202789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4149686661/10000000000 : ℝ)|^4325 ≤ (3948482494619/12500000000000 : ℝ)^3301
        have hw : |(4149686661/10000000000 : ℝ)|=(4149686661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1365_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11203/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14721/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7361/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5601/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7361/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5601/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7361/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5601/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7361/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5601/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7361/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5601/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7361/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5601/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5601/50000 : ℝ) ^ (1081/256 : ℝ) ≤ (9671681577147733/100000000000000000000 : ℝ) := by
    have hpowers : (5601/50000 : ℝ)^1081 ≤ (9671681577147733/100000000000000000000 : ℝ)^256 := by
      have hnat : (5601 : ℕ)^1081*100000000000000000000^256 ≤ 9671681577147733^256*50000^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5601 50000 9671681577147733 100000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5601/50000 : ℝ)) (X := (9671681577147733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7361/50000 : ℝ) ^ (1081/256 : ℝ) ≤ (30662662610695181/100000000000000000000 : ℝ) := by
    have hpowers : (7361/50000 : ℝ)^1081 ≤ (30662662610695181/100000000000000000000 : ℝ)^256 := by
      have hnat : (7361 : ℕ)^1081*100000000000000000000^256 ≤ 30662662610695181^256*50000^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7361 50000 30662662610695181 100000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7361/50000 : ℝ)) (X := (30662662610695181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009671681577147733/50000000000000000000 : ℝ) ≤ (1250057256423411/1250000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (50009671681577147733/50000000000000000000 : ℝ)^256 ≤ (1250057256423411/1250000000000000 : ℝ)^1081 := by
      have hnat : (50009671681577147733 : ℕ)^256*1250000000000000^1081 ≤ 1250057256423411^1081*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009671681577147733 50000000000000000000 1250057256423411 1250000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250057256423411/1250000000000000 : ℝ)) (X := (50009671681577147733/50000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020167172093921457/50000000000000000000 : ℝ) ≤ (10000955041929079/10000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (50020167172093921457/50000000000000000000 : ℝ)^256 ≤ (10000955041929079/10000000000000000 : ℝ)^1081 := by
      have hnat : (50020167172093921457 : ℕ)^256*10000000000000000^1081 ≤ 10000955041929079^1081*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020167172093921457 50000000000000000000 10000955041929079 10000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000955041929079/10000000000000000 : ℝ)) (X := (50020167172093921457/50000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030662662610695181/50000000000000000000 : ℝ) ≤ (1000145203247087/1000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (50030662662610695181/50000000000000000000 : ℝ)^256 ≤ (1000145203247087/1000000000000000 : ℝ)^1081 := by
      have hnat : (50030662662610695181 : ℕ)^256*1000000000000000^1081 ≤ 1000145203247087^1081*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030662662610695181 50000000000000000000 1000145203247087 1000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000145203247087/1000000000000000 : ℝ)) (X := (50030662662610695181/50000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9671681577147733/100000000000000000000 : ℝ) ≤ ((8797619441196242049/8800000000000000000 : ℝ)+2*(496990541791/352000000000000 : ℝ)*(5601/50000 : ℝ))^(1081/256 : ℝ) := by
    rw [show (8797619441196242049/8800000000000000000 : ℝ)+2*(496990541791/352000000000000 : ℝ)*(5601/50000 : ℝ)=(1250057256423411/1250000000000000 : ℝ) by norm_num, show 1+2*(9671681577147733/100000000000000000000 : ℝ)=(50009671681577147733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30662662610695181/100000000000000000000 : ℝ)+(9671681577147733/100000000000000000000 : ℝ) ≤ ((8797619441196242049/8800000000000000000 : ℝ)+(496990541791/352000000000000 : ℝ)*((7361/50000 : ℝ)+(5601/50000 : ℝ)))^(1081/256 : ℝ) := by
    rw [show (8797619441196242049/8800000000000000000 : ℝ)+(496990541791/352000000000000 : ℝ)*((7361/50000 : ℝ)+(5601/50000 : ℝ))=(10000955041929079/10000000000000000 : ℝ) by norm_num, show 1+(30662662610695181/100000000000000000000 : ℝ)+(9671681577147733/100000000000000000000 : ℝ)=(50020167172093921457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30662662610695181/100000000000000000000 : ℝ) ≤ ((8797619441196242049/8800000000000000000 : ℝ)+2*(496990541791/352000000000000 : ℝ)*(7361/50000 : ℝ))^(1081/256 : ℝ) := by
    rw [show (8797619441196242049/8800000000000000000 : ℝ)+2*(496990541791/352000000000000 : ℝ)*(7361/50000 : ℝ)=(1000145203247087/1000000000000000 : ℝ) by norm_num, show 1+2*(30662662610695181/100000000000000000000 : ℝ)=(50030662662610695181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8797619441196242049/8800000000000000000 : ℝ)*(X 1 0+X 2 0)+(496990541791/352000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (5601/50000 : ℝ)) (hi := (7361/50000 : ℝ)) (c := (8797619441196242049/8800000000000000000 : ℝ)) (alpha := (496990541791/352000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8797619441196242049/8800000000000000000 : ℝ)*(X 0 1+X 2 1)+(496990541791/352000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (5601/50000 : ℝ)) (hi := (7361/50000 : ℝ)) (c := (8797619441196242049/8800000000000000000 : ℝ)) (alpha := (496990541791/352000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8797619441196242049/8800000000000000000 : ℝ)*(X 0 2+X 1 2)+(496990541791/352000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (5601/50000 : ℝ)) (hi := (7361/50000 : ℝ)) (c := (8797619441196242049/8800000000000000000 : ℝ)) (alpha := (496990541791/352000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2024267533/10000000000 : ℝ)*X 0 0+(5411481709/10000000000 : ℝ)*X 0 1+(163916431/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348579893/10000000000 : ℝ)*X 1 0+(-421781319/2000000000 : ℝ)*X 1 1+(5245325761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674289941/5000000000 : ℝ)*X 2 0+(5245325767/10000000000 : ℝ)*X 2 1+(-1054453301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4320643491/10000000000 : ℝ)*X 0 0+(103710539/250000000 : ℝ)*X 0 1+(2249730653/5000000000 : ℝ)*X 0 2+(4320643491/10000000000 : ℝ)*X 1 0+(103710539/250000000 : ℝ)*X 1 1+(2249730653/5000000000 : ℝ)*X 1 2+(4320643491/10000000000 : ℝ)*X 2 0+(103710539/250000000 : ℝ)*X 2 1+(2249730653/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-404855903/2000000000 : ℝ)*X 0 0+(2622960733/5000000000 : ℝ)*X 0 1+(5410882917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326417633/2500000000 : ℝ)*X 1 0+(-971674717/5000000000 : ℝ)*X 1 1+(5410882939/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305670537/10000000000 : ℝ)*X 2 0+(2705441479/5000000000 : ℝ)*X 2 1+(-971674701/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080167147/2500000000 : ℝ)*X 0 0+(4498202789/10000000000 : ℝ)*X 0 1+(4149686661/10000000000 : ℝ)*X 0 2+(1080167147/2500000000 : ℝ)*X 1 0+(4498202789/10000000000 : ℝ)*X 1 1+(4149686661/10000000000 : ℝ)*X 1 2+(1080167147/2500000000 : ℝ)*X 2 0+(4498202789/10000000000 : ℝ)*X 2 1+(4149686661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (180257677783107944497622097/44000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (748212227/100000000000000 : ℝ)*(base19) + (119906877/20000000000000 : ℝ)*(base23) + (36450607/50000000000000 : ℝ)*(lower2) + (132113217/100000000000000 : ℝ)*(upper3) + (21320643/100000000000000 : ℝ)*(upper5) + (886716507531351/20000000000000 : ℝ)*(major0) + (886716507531351/20000000000000 : ℝ)*(major1) + (886716507531351/20000000000000 : ℝ)*(major2) + (376153651944321/6250000000000 : ℝ)*(sp0) + (1203694012825137/20000000000000 : ℝ)*(sp1) + (6018470212803527/100000000000000 : ℝ)*(sp2) + (284868610015609/10000000000000 : ℝ)*(sp3) + (1547653597/12500000000000 : ℝ)*(sp4) + (501641291/6250000000000 : ℝ)*(sp7) + (569738825283349/20000000000000 : ℝ)*(f.failure) + (752308851542239/12500000000000 : ℝ)*(f.sum) + (21854261151159/3520000000000000000000000000 : ℝ)*base66 + (262828476230996801/176000000000000000000000000000000 : ℝ)*base68 + (2022625976966996801/176000000000000000000000000000000 : ℝ)*base70 + (30308997654996801/176000000000000000000000000000000 : ℝ)*base72 + (1874384290039/3520000000000000000000000000 : ℝ)*base74 + (1268891189622996801/176000000000000000000000000000000 : ℝ)*base76 + (719347608838996801/176000000000000000000000000000000 : ℝ)*base78 + (448302838025003199/176000000000000000000000000000000 : ℝ)*base79 + (20292082025399/3520000000000000000000000000 : ℝ)*base82 + (1243853/500000000000000000000 : ℝ)*base90 + (1243853/500000000000000000000 : ℝ)*base92 + (1243853/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28140667653910213413992127/2750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (866374157/50000000000000 : ℝ)*(base19) + (3734127/200000000000 : ℝ)*(base23) + (595761773/100000000000000 : ℝ)*(lower1) + (53188267/25000000000000 : ℝ)*(upper3) + (13053913/25000000000000 : ℝ)*(lower4) + (100052661/50000000000000 : ℝ)*(upper5) + (55820472354159/1250000000000 : ℝ)*(major0) + (55820472354159/1250000000000 : ℝ)*(major1) + (55820472354159/1250000000000 : ℝ)*(major2) + (3732656159/100000000000000 : ℝ)*(sp2) + (6061984762167091/100000000000000 : ℝ)*(sp4) + (6061983029418777/100000000000000 : ℝ)*(sp5) + (757747395305929/12500000000000 : ℝ)*(sp6) + (1434645236699657/50000000000000 : ℝ)*(sp7) + (1434645236699657/50000000000000 : ℝ)*(f.failure) + (6061984762167091/100000000000000 : ℝ)*(f.sum) + (640978450029/220000000000000000000000000 : ℝ)*base65 + (77834917313056791/11000000000000000000000000000000 : ℝ)*base67 + (51937915974056791/11000000000000000000000000000000 : ℝ)*base69 + (1697915293029056791/11000000000000000000000000000000 : ℝ)*base71 + (57657962609/220000000000000000000000000 : ℝ)*base73 + (1102666756741943209/11000000000000000000000000000000 : ℝ)*base76 + (146825919591056791/11000000000000000000000000000000 : ℝ)*base77 + (229877605880056791/11000000000000000000000000000000 : ℝ)*base79 + (1080641539071/220000000000000000000000000 : ℝ)*base82 + (5653729/1250000000000000000000 : ℝ)*base90 + (5653729/1250000000000000000000 : ℝ)*base92 + (5653729/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1365_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5601/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1365_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1365_box_0 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-46470369/250000000 : ℝ)*x 0 + (1077795373/2000000000 : ℝ)*x 1 + (5388977411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46470369/250000000 : ℝ)^4325 ≤ (11029264638161/100000000000000 : ℝ)^3301 := by
    have hnat : (46470369 : ℕ)^4325*100000000000000^3301 ≤ 11029264638161^3301*250000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46470369 250000000 11029264638161 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077795373/2000000000 : ℝ)^4325 ≤ (44485364717527/100000000000000 : ℝ)^3301 := by
    have hnat : (1077795373 : ℕ)^4325*100000000000000^3301 ≤ 44485364717527^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077795373 2000000000 44485364717527 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388977411/10000000000 : ℝ)^4325 ≤ (5560671327857/12500000000000 : ℝ)^3301 := by
    have hnat : (5388977411 : ℕ)^4325*12500000000000^3301 ≤ 5560671327857^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388977411 10000000000 5560671327857 12500000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-46470369/250000000 : ℝ), (1077795373/2000000000 : ℝ), (5388977411/10000000000 : ℝ)] ![(11029264638161/100000000000000 : ℝ), (44485364717527/100000000000000 : ℝ), (5560671327857/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-46470369/250000000 : ℝ)|^4325 ≤ (11029264638161/100000000000000 : ℝ)^3301
        have hw : |(-46470369/250000000 : ℝ)|=(46470369/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077795373/2000000000 : ℝ)|^4325 ≤ (44485364717527/100000000000000 : ℝ)^3301
        have hw : |(1077795373/2000000000 : ℝ)|=(1077795373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388977411/10000000000 : ℝ)|^4325 ≤ (5560671327857/12500000000000 : ℝ)^3301
        have hw : |(5388977411/10000000000 : ℝ)|=(5388977411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_box_1 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285459663/10000000000 : ℝ)*x 0 + (-1000374481/5000000000 : ℝ)*x 1 + (2694488397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285459663/10000000000 : ℝ)^4325 ≤ (8673822520061/20000000000000 : ℝ)^3301 := by
    have hnat : (5285459663 : ℕ)^4325*20000000000000^3301 ≤ 8673822520061^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285459663 10000000000 8673822520061 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1000374481/5000000000 : ℝ)^4325 ≤ (3036380858801/25000000000000 : ℝ)^3301 := by
    have hnat : (1000374481 : ℕ)^4325*25000000000000^3301 ≤ 3036380858801^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000374481 5000000000 3036380858801 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2694488397/5000000000 : ℝ)^4325 ≤ (22242681974809/50000000000000 : ℝ)^3301 := by
    have hnat : (2694488397 : ℕ)^4325*50000000000000^3301 ≤ 22242681974809^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694488397 5000000000 22242681974809 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285459663/10000000000 : ℝ), (-1000374481/5000000000 : ℝ), (2694488397/5000000000 : ℝ)] ![(8673822520061/20000000000000 : ℝ), (3036380858801/25000000000000 : ℝ), (22242681974809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285459663/10000000000 : ℝ)|^4325 ≤ (8673822520061/20000000000000 : ℝ)^3301
        have hw : |(5285459663/10000000000 : ℝ)|=(5285459663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1000374481/5000000000 : ℝ)|^4325 ≤ (3036380858801/25000000000000 : ℝ)^3301
        have hw : |(-1000374481/5000000000 : ℝ)|=(1000374481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2694488397/5000000000 : ℝ)|^4325 ≤ (22242681974809/50000000000000 : ℝ)^3301
        have hw : |(2694488397/5000000000 : ℝ)|=(2694488397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_box_2 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642729741/5000000000 : ℝ)*x 0 + (538897693/1000000000 : ℝ)*x 1 + (-2000749021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642729741/5000000000 : ℝ)^4325 ≤ (43369110654421/100000000000000 : ℝ)^3301 := by
    have hnat : (2642729741 : ℕ)^4325*100000000000000^3301 ≤ 43369110654421^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642729741 5000000000 43369110654421 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538897693/1000000000 : ℝ)^4325 ≤ (22242682710271/50000000000000 : ℝ)^3301 := by
    have hnat : (538897693 : ℕ)^4325*50000000000000^3301 ≤ 22242682710271^3301*1000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538897693 1000000000 22242682710271 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2000749021/10000000000 : ℝ)^4325 ≤ (12145523904467/100000000000000 : ℝ)^3301 := by
    have hnat : (2000749021 : ℕ)^4325*100000000000000^3301 ≤ 12145523904467^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000749021 10000000000 12145523904467 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642729741/5000000000 : ℝ), (538897693/1000000000 : ℝ), (-2000749021/10000000000 : ℝ)] ![(43369110654421/100000000000000 : ℝ), (22242682710271/50000000000000 : ℝ), (12145523904467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642729741/5000000000 : ℝ)|^4325 ≤ (43369110654421/100000000000000 : ℝ)^3301
        have hw : |(2642729741/5000000000 : ℝ)|=(2642729741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538897693/1000000000 : ℝ)|^4325 ≤ (22242682710271/50000000000000 : ℝ)^3301
        have hw : |(538897693/1000000000 : ℝ)|=(538897693/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2000749021/10000000000 : ℝ)|^4325 ≤ (12145523904467/100000000000000 : ℝ)^3301
        have hw : |(-2000749021/10000000000 : ℝ)|=(2000749021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_box_3 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4468305459/10000000000 : ℝ)*x 0 + (531331423/1250000000 : ℝ)*x 1 + (2125325819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4468305459/10000000000 : ℝ)^4325 ≤ (17401392934817/50000000000000 : ℝ)^3301 := by
    have hnat : (4468305459 : ℕ)^4325*50000000000000^3301 ≤ 17401392934817^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4468305459 10000000000 17401392934817 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531331423/1250000000 : ℝ)^4325 ≤ (32598605787239/100000000000000 : ℝ)^3301 := by
    have hnat : (531331423 : ℕ)^4325*100000000000000^3301 ≤ 32598605787239^3301*1250000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531331423 1250000000 32598605787239 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125325819/5000000000 : ℝ)^4325 ≤ (32598608339457/100000000000000 : ℝ)^3301 := by
    have hnat : (2125325819 : ℕ)^4325*100000000000000^3301 ≤ 32598608339457^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125325819 5000000000 32598608339457 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4468305459/10000000000 : ℝ), (531331423/1250000000 : ℝ), (2125325819/5000000000 : ℝ)] ![(17401392934817/50000000000000 : ℝ), (32598605787239/100000000000000 : ℝ), (32598608339457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4468305459/10000000000 : ℝ)|^4325 ≤ (17401392934817/50000000000000 : ℝ)^3301
        have hw : |(4468305459/10000000000 : ℝ)|=(4468305459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(531331423/1250000000 : ℝ)|^4325 ≤ (32598605787239/100000000000000 : ℝ)^3301
        have hw : |(531331423/1250000000 : ℝ)|=(531331423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2125325819/5000000000 : ℝ)|^4325 ≤ (32598608339457/100000000000000 : ℝ)^3301
        have hw : |(2125325819/5000000000 : ℝ)|=(2125325819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_box_4 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1096233663/5000000000 : ℝ)*x 0 + (658176599/1250000000 : ℝ)*x 1 + (329088293/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1096233663/5000000000 : ℝ)^4325 ≤ (3423139876393/25000000000000 : ℝ)^3301 := by
    have hnat : (1096233663 : ℕ)^4325*25000000000000^3301 ≤ 3423139876393^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096233663 5000000000 3423139876393 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658176599/1250000000 : ℝ)^4325 ≤ (4315372079881/10000000000000 : ℝ)^3301 := by
    have hnat : (658176599 : ℕ)^4325*10000000000000^3301 ≤ 4315372079881^3301*1250000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658176599 1250000000 4315372079881 10000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329088293/625000000 : ℝ)^4325 ≤ (43153719682051/100000000000000 : ℝ)^3301 := by
    have hnat : (329088293 : ℕ)^4325*100000000000000^3301 ≤ 43153719682051^3301*625000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329088293 625000000 43153719682051 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1096233663/5000000000 : ℝ), (658176599/1250000000 : ℝ), (329088293/625000000 : ℝ)] ![(3423139876393/25000000000000 : ℝ), (4315372079881/10000000000000 : ℝ), (43153719682051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1096233663/5000000000 : ℝ)|^4325 ≤ (3423139876393/25000000000000 : ℝ)^3301
        have hw : |(-1096233663/5000000000 : ℝ)|=(1096233663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658176599/1250000000 : ℝ)|^4325 ≤ (4315372079881/10000000000000 : ℝ)^3301
        have hw : |(658176599/1250000000 : ℝ)|=(658176599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329088293/625000000 : ℝ)|^4325 ≤ (43153719682051/100000000000000 : ℝ)^3301
        have hw : |(329088293/625000000 : ℝ)|=(329088293/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_box_5 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343041147/2500000000 : ℝ)*x 0 + (-1025245239/5000000000 : ℝ)*x 1 + (5265412483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343041147/2500000000 : ℝ)^4325 ≤ (5537952195959/12500000000000 : ℝ)^3301 := by
    have hnat : (1343041147 : ℕ)^4325*12500000000000^3301 ≤ 5537952195959^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343041147 2500000000 5537952195959 12500000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025245239/5000000000 : ℝ)^4325 ≤ (3135666234627/25000000000000 : ℝ)^3301 := by
    have hnat : (1025245239 : ℕ)^4325*25000000000000^3301 ≤ 3135666234627^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025245239 5000000000 3135666234627 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265412483/10000000000 : ℝ)^4325 ≤ (8630743496149/20000000000000 : ℝ)^3301 := by
    have hnat : (5265412483 : ℕ)^4325*20000000000000^3301 ≤ 8630743496149^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265412483 10000000000 8630743496149 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343041147/2500000000 : ℝ), (-1025245239/5000000000 : ℝ), (5265412483/10000000000 : ℝ)] ![(5537952195959/12500000000000 : ℝ), (3135666234627/25000000000000 : ℝ), (8630743496149/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343041147/2500000000 : ℝ)|^4325 ≤ (5537952195959/12500000000000 : ℝ)^3301
        have hw : |(1343041147/2500000000 : ℝ)|=(1343041147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1025245239/5000000000 : ℝ)|^4325 ≤ (3135666234627/25000000000000 : ℝ)^3301
        have hw : |(-1025245239/5000000000 : ℝ)|=(1025245239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265412483/10000000000 : ℝ)|^4325 ≤ (8630743496149/20000000000000 : ℝ)^3301
        have hw : |(5265412483/10000000000 : ℝ)|=(5265412483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_box_6 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343041153/2500000000 : ℝ)*x 0 + (658176583/1250000000 : ℝ)*x 1 + (-512622551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343041153/2500000000 : ℝ)^4325 ≤ (11075904456749/25000000000000 : ℝ)^3301 := by
    have hnat : (1343041153 : ℕ)^4325*25000000000000^3301 ≤ 11075904456749^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343041153 2500000000 11075904456749 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658176583/1250000000 : ℝ)^4325 ≤ (43153719424337/100000000000000 : ℝ)^3301 := by
    have hnat : (658176583 : ℕ)^4325*100000000000000^3301 ≤ 43153719424337^3301*1250000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658176583 1250000000 43153719424337 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512622551/2500000000 : ℝ)^4325 ≤ (2508532548511/20000000000000 : ℝ)^3301 := by
    have hnat : (512622551 : ℕ)^4325*20000000000000^3301 ≤ 2508532548511^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512622551 2500000000 2508532548511 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343041153/2500000000 : ℝ), (658176583/1250000000 : ℝ), (-512622551/2500000000 : ℝ)] ![(11075904456749/25000000000000 : ℝ), (43153719424337/100000000000000 : ℝ), (2508532548511/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343041153/2500000000 : ℝ)|^4325 ≤ (11075904456749/25000000000000 : ℝ)^3301
        have hw : |(1343041153/2500000000 : ℝ)|=(1343041153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658176583/1250000000 : ℝ)|^4325 ≤ (43153719424337/100000000000000 : ℝ)^3301
        have hw : |(658176583/1250000000 : ℝ)|=(658176583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-512622551/2500000000 : ℝ)|^4325 ≤ (2508532548511/20000000000000 : ℝ)^3301
        have hw : |(-512622551/2500000000 : ℝ)|=(512622551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_box_7 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2086011291/5000000000 : ℝ)*x 0 + (2199370081/5000000000 : ℝ)*x 1 + (2199370031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086011291/5000000000 : ℝ)^4325 ≤ (15905405966897/50000000000000 : ℝ)^3301 := by
    have hnat : (2086011291 : ℕ)^4325*50000000000000^3301 ≤ 15905405966897^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086011291 5000000000 15905405966897 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2199370081/5000000000 : ℝ)^4325 ≤ (34094594528871/100000000000000 : ℝ)^3301 := by
    have hnat : (2199370081 : ℕ)^4325*100000000000000^3301 ≤ 34094594528871^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199370081 5000000000 34094594528871 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2199370031/5000000000 : ℝ)^4325 ≤ (34094593513329/100000000000000 : ℝ)^3301 := by
    have hnat : (2199370031 : ℕ)^4325*100000000000000^3301 ≤ 34094593513329^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199370031 5000000000 34094593513329 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2086011291/5000000000 : ℝ), (2199370081/5000000000 : ℝ), (2199370031/5000000000 : ℝ)] ![(15905405966897/50000000000000 : ℝ), (34094594528871/100000000000000 : ℝ), (34094593513329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2086011291/5000000000 : ℝ)|^4325 ≤ (15905405966897/50000000000000 : ℝ)^3301
        have hw : |(2086011291/5000000000 : ℝ)|=(2086011291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2199370081/5000000000 : ℝ)|^4325 ≤ (34094594528871/100000000000000 : ℝ)^3301
        have hw : |(2199370081/5000000000 : ℝ)|=(2199370081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2199370031/5000000000 : ℝ)|^4325 ≤ (34094593513329/100000000000000 : ℝ)^3301
        have hw : |(2199370031/5000000000 : ℝ)|=(2199370031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_box_8 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2122341941/10000000000 : ℝ)*x 0 + (80941243/156250000 : ℝ)*x 1 + (5402987003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122341941/10000000000 : ℝ)^4325 ≤ (6560809190347/50000000000000 : ℝ)^3301 := by
    have hnat : (2122341941 : ℕ)^4325*50000000000000^3301 ≤ 6560809190347^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122341941 10000000000 6560809190347 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80941243/156250000 : ℝ)^4325 ≤ (42241427494147/100000000000000 : ℝ)^3301 := by
    have hnat : (80941243 : ℕ)^4325*100000000000000^3301 ≤ 42241427494147^3301*156250000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80941243 156250000 42241427494147 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402987003/10000000000 : ℝ)^4325 ≤ (8927390822583/20000000000000 : ℝ)^3301 := by
    have hnat : (5402987003 : ℕ)^4325*20000000000000^3301 ≤ 8927390822583^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402987003 10000000000 8927390822583 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2122341941/10000000000 : ℝ), (80941243/156250000 : ℝ), (5402987003/10000000000 : ℝ)] ![(6560809190347/50000000000000 : ℝ), (42241427494147/100000000000000 : ℝ), (8927390822583/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2122341941/10000000000 : ℝ)|^4325 ≤ (6560809190347/50000000000000 : ℝ)^3301
        have hw : |(-2122341941/10000000000 : ℝ)|=(2122341941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80941243/156250000 : ℝ)|^4325 ≤ (42241427494147/100000000000000 : ℝ)^3301
        have hw : |(80941243/156250000 : ℝ)|=(80941243/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402987003/10000000000 : ℝ)|^4325 ≤ (8927390822583/20000000000000 : ℝ)^3301
        have hw : |(5402987003/10000000000 : ℝ)|=(5402987003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_box_9 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329726489/625000000 : ℝ)*x 0 + (-3896443/19531250 : ℝ)*x 1 + (5402986521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329726489/625000000 : ℝ)^4325 ≤ (21631700293233/50000000000000 : ℝ)^3301 := by
    have hnat : (329726489 : ℕ)^4325*50000000000000^3301 ≤ 21631700293233^3301*625000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329726489 625000000 21631700293233 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3896443/19531250 : ℝ)^4325 ≤ (12099650494211/100000000000000 : ℝ)^3301 := by
    have hnat : (3896443 : ℕ)^4325*100000000000000^3301 ≤ 12099650494211^3301*19531250^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3896443 19531250 12099650494211 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402986521/10000000000 : ℝ)^4325 ≤ (22318474447793/50000000000000 : ℝ)^3301 := by
    have hnat : (5402986521 : ℕ)^4325*50000000000000^3301 ≤ 22318474447793^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402986521 10000000000 22318474447793 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329726489/625000000 : ℝ), (-3896443/19531250 : ℝ), (5402986521/10000000000 : ℝ)] ![(21631700293233/50000000000000 : ℝ), (12099650494211/100000000000000 : ℝ), (22318474447793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329726489/625000000 : ℝ)|^4325 ≤ (21631700293233/50000000000000 : ℝ)^3301
        have hw : |(329726489/625000000 : ℝ)|=(329726489/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3896443/19531250 : ℝ)|^4325 ≤ (12099650494211/100000000000000 : ℝ)^3301
        have hw : |(-3896443/19531250 : ℝ)|=(3896443/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402986521/10000000000 : ℝ)|^4325 ≤ (22318474447793/50000000000000 : ℝ)^3301
        have hw : |(5402986521/10000000000 : ℝ)|=(5402986521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_box_10 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275623831/10000000000 : ℝ)*x 0 + (5402986583/10000000000 : ℝ)*x 1 + (-498744681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275623831/10000000000 : ℝ)^4325 ≤ (21631700330839/50000000000000 : ℝ)^3301 := by
    have hnat : (5275623831 : ℕ)^4325*50000000000000^3301 ≤ 21631700330839^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275623831 10000000000 21631700330839 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402986583/10000000000 : ℝ)^4325 ≤ (22318474783347/50000000000000 : ℝ)^3301 := by
    have hnat : (5402986583 : ℕ)^4325*50000000000000^3301 ≤ 22318474783347^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402986583 10000000000 22318474783347 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (498744681/2500000000 : ℝ)^4325 ≤ (2419929952627/20000000000000 : ℝ)^3301 := by
    have hnat : (498744681 : ℕ)^4325*20000000000000^3301 ≤ 2419929952627^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498744681 2500000000 2419929952627 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275623831/10000000000 : ℝ), (5402986583/10000000000 : ℝ), (-498744681/2500000000 : ℝ)] ![(21631700330839/50000000000000 : ℝ), (22318474783347/50000000000000 : ℝ), (2419929952627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275623831/10000000000 : ℝ)|^4325 ≤ (21631700330839/50000000000000 : ℝ)^3301
        have hw : |(5275623831/10000000000 : ℝ)|=(5275623831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402986583/10000000000 : ℝ)|^4325 ≤ (22318474783347/50000000000000 : ℝ)^3301
        have hw : |(5402986583/10000000000 : ℝ)|=(5402986583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-498744681/2500000000 : ℝ)|^4325 ≤ (2419929952627/20000000000000 : ℝ)^3301
        have hw : |(-498744681/2500000000 : ℝ)|=(498744681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_box_11 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4501338551/10000000000 : ℝ)*x 0 + (4233847581/10000000000 : ℝ)*x 1 + (2116923811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4501338551/10000000000 : ℝ)^4325 ≤ (35140273473047/100000000000000 : ℝ)^3301 := by
    have hnat : (4501338551 : ℕ)^4325*100000000000000^3301 ≤ 35140273473047^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501338551 10000000000 35140273473047 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233847581/10000000000 : ℝ)^4325 ≤ (32429863050207/100000000000000 : ℝ)^3301 := by
    have hnat : (4233847581 : ℕ)^4325*100000000000000^3301 ≤ 32429863050207^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233847581 10000000000 32429863050207 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116923811/5000000000 : ℝ)^4325 ≤ (32429863461673/100000000000000 : ℝ)^3301 := by
    have hnat : (2116923811 : ℕ)^4325*100000000000000^3301 ≤ 32429863461673^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116923811 5000000000 32429863461673 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4501338551/10000000000 : ℝ), (4233847581/10000000000 : ℝ), (2116923811/5000000000 : ℝ)] ![(35140273473047/100000000000000 : ℝ), (32429863050207/100000000000000 : ℝ), (32429863461673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4501338551/10000000000 : ℝ)|^4325 ≤ (35140273473047/100000000000000 : ℝ)^3301
        have hw : |(4501338551/10000000000 : ℝ)|=(4501338551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233847581/10000000000 : ℝ)|^4325 ≤ (32429863050207/100000000000000 : ℝ)^3301
        have hw : |(4233847581/10000000000 : ℝ)|=(4233847581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2116923811/5000000000 : ℝ)|^4325 ≤ (32429863461673/100000000000000 : ℝ)^3301
        have hw : |(2116923811/5000000000 : ℝ)|=(2116923811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_box_12 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-482308409/2500000000 : ℝ)*x 0 + (2735997737/5000000000 : ℝ)*x 1 + (5254325289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (482308409/2500000000 : ℝ)^4325 ≤ (5789949170043/50000000000000 : ℝ)^3301 := by
    have hnat : (482308409 : ℕ)^4325*50000000000000^3301 ≤ 5789949170043^3301*2500000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482308409 2500000000 5789949170043 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735997737/5000000000 : ℝ)^4325 ≤ (45385400362557/100000000000000 : ℝ)^3301 := by
    have hnat : (2735997737 : ℕ)^4325*100000000000000^3301 ≤ 45385400362557^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735997737 5000000000 45385400362557 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254325289/10000000000 : ℝ)^4325 ≤ (10758675317583/25000000000000 : ℝ)^3301 := by
    have hnat : (5254325289 : ℕ)^4325*25000000000000^3301 ≤ 10758675317583^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254325289 10000000000 10758675317583 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-482308409/2500000000 : ℝ), (2735997737/5000000000 : ℝ), (5254325289/10000000000 : ℝ)] ![(5789949170043/50000000000000 : ℝ), (45385400362557/100000000000000 : ℝ), (10758675317583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-482308409/2500000000 : ℝ)|^4325 ≤ (5789949170043/50000000000000 : ℝ)^3301
        have hw : |(-482308409/2500000000 : ℝ)|=(482308409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735997737/5000000000 : ℝ)|^4325 ≤ (45385400362557/100000000000000 : ℝ)^3301
        have hw : |(2735997737/5000000000 : ℝ)|=(2735997737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254325289/10000000000 : ℝ)|^4325 ≤ (10758675317583/25000000000000 : ℝ)^3301
        have hw : |(5254325289/10000000000 : ℝ)|=(5254325289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_box_13 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075988519/2000000000 : ℝ)*x 0 + (-2054850639/10000000000 : ℝ)*x 1 + (5254325209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075988519/2000000000 : ℝ)^4325 ≤ (11096919725587/25000000000000 : ℝ)^3301 := by
    have hnat : (1075988519 : ℕ)^4325*25000000000000^3301 ≤ 11096919725587^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075988519 2000000000 11096919725587 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2054850639/10000000000 : ℝ)^4325 ≤ (12577620664009/100000000000000 : ℝ)^3301 := by
    have hnat : (2054850639 : ℕ)^4325*100000000000000^3301 ≤ 12577620664009^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054850639 10000000000 12577620664009 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254325209/10000000000 : ℝ)^4325 ≤ (5379337551481/12500000000000 : ℝ)^3301 := by
    have hnat : (5254325209 : ℕ)^4325*12500000000000^3301 ≤ 5379337551481^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254325209 10000000000 5379337551481 12500000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075988519/2000000000 : ℝ), (-2054850639/10000000000 : ℝ), (5254325209/10000000000 : ℝ)] ![(11096919725587/25000000000000 : ℝ), (12577620664009/100000000000000 : ℝ), (5379337551481/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075988519/2000000000 : ℝ)|^4325 ≤ (11096919725587/25000000000000 : ℝ)^3301
        have hw : |(1075988519/2000000000 : ℝ)|=(1075988519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2054850639/10000000000 : ℝ)|^4325 ≤ (12577620664009/100000000000000 : ℝ)^3301
        have hw : |(-2054850639/10000000000 : ℝ)|=(2054850639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254325209/10000000000 : ℝ)|^4325 ≤ (5379337551481/12500000000000 : ℝ)^3301
        have hw : |(5254325209/10000000000 : ℝ)|=(5254325209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_box_14 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689971227/5000000000 : ℝ)*x 0 + (2627162693/5000000000 : ℝ)*x 1 + (-2054850593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689971227/5000000000 : ℝ)^4325 ≤ (44387677378139/100000000000000 : ℝ)^3301 := by
    have hnat : (2689971227 : ℕ)^4325*100000000000000^3301 ≤ 44387677378139^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689971227 5000000000 44387677378139 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627162693/5000000000 : ℝ)^4325 ≤ (10758675577811/25000000000000 : ℝ)^3301 := by
    have hnat : (2627162693 : ℕ)^4325*25000000000000^3301 ≤ 10758675577811^3301*5000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627162693 5000000000 10758675577811 25000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2054850593/10000000000 : ℝ)^4325 ≤ (6288810147551/50000000000000 : ℝ)^3301 := by
    have hnat : (2054850593 : ℕ)^4325*50000000000000^3301 ≤ 6288810147551^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054850593 10000000000 6288810147551 50000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689971227/5000000000 : ℝ), (2627162693/5000000000 : ℝ), (-2054850593/10000000000 : ℝ)] ![(44387677378139/100000000000000 : ℝ), (10758675577811/25000000000000 : ℝ), (6288810147551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689971227/5000000000 : ℝ)|^4325 ≤ (44387677378139/100000000000000 : ℝ)^3301
        have hw : |(2689971227/5000000000 : ℝ)|=(2689971227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627162693/5000000000 : ℝ)|^4325 ≤ (10758675577811/25000000000000 : ℝ)^3301
        have hw : |(2627162693/5000000000 : ℝ)|=(2627162693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2054850593/10000000000 : ℝ)|^4325 ≤ (6288810147551/50000000000000 : ℝ)^3301
        have hw : |(-2054850593/10000000000 : ℝ)|=(2054850593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1365_box_15 (p : ℝ) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4144989063/10000000000 : ℝ)*x 0 + (882403447/2000000000 : ℝ)*x 1 + (176480687/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4144989063/10000000000 : ℝ)^4325 ≤ (31541016918903/100000000000000 : ℝ)^3301 := by
    have hnat : (4144989063 : ℕ)^4325*100000000000000^3301 ≤ 31541016918903^3301*10000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144989063 10000000000 31541016918903 100000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (882403447/2000000000 : ℝ)^4325 ≤ (3422949183743/10000000000000 : ℝ)^3301 := by
    have hnat : (882403447 : ℕ)^4325*10000000000000^3301 ≤ 3422949183743^3301*2000000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882403447 2000000000 3422949183743 10000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176480687/400000000 : ℝ)^4325 ≤ (6845898245507/20000000000000 : ℝ)^3301 := by
    have hnat : (176480687 : ℕ)^4325*20000000000000^3301 ≤ 6845898245507^3301*400000000^4325 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176480687 400000000 6845898245507 20000000000000 4325 3301 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4325/1024 : ℝ)) 4325 3301 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4144989063/10000000000 : ℝ), (882403447/2000000000 : ℝ), (176480687/400000000 : ℝ)] ![(31541016918903/100000000000000 : ℝ), (3422949183743/10000000000000 : ℝ), (6845898245507/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4144989063/10000000000 : ℝ)|^4325 ≤ (31541016918903/100000000000000 : ℝ)^3301
        have hw : |(4144989063/10000000000 : ℝ)|=(4144989063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(882403447/2000000000 : ℝ)|^4325 ≤ (3422949183743/10000000000000 : ℝ)^3301
        have hw : |(882403447/2000000000 : ℝ)|=(882403447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(176480687/400000000 : ℝ)|^4325 ≤ (6845898245507/20000000000000 : ℝ)^3301
        have hw : |(176480687/400000000 : ℝ)|=(176480687/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1365_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12573/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29493/50000 : ℝ) ∧ (10011/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84441/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14721/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11203/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14721/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11203/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14721/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11203/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14721/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11203/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14721/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11203/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14721/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11203/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11203/100000 : ℝ) ^ (1081/256 : ℝ) ≤ (1935065579161363/20000000000000000000 : ℝ) := by
    have hpowers : (11203/100000 : ℝ)^1081 ≤ (1935065579161363/20000000000000000000 : ℝ)^256 := by
      have hnat : (11203 : ℕ)^1081*20000000000000000000^256 ≤ 1935065579161363^256*100000^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11203 100000 1935065579161363 20000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11203/100000 : ℝ)) (X := (1935065579161363/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14721/100000 : ℝ) ^ (1081/256 : ℝ) ≤ (30653868716303963/100000000000000000000 : ℝ) := by
    have hpowers : (14721/100000 : ℝ)^1081 ≤ (30653868716303963/100000000000000000000 : ℝ)^256 := by
      have hnat : (14721 : ℕ)^1081*100000000000000000000^256 ≤ 30653868716303963^256*100000^1081 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14721 100000 30653868716303963 100000000000000000000 1081 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14721/100000 : ℝ)) (X := (30653868716303963/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001935065579161363/10000000000000000000 : ℝ) ≤ (10000458224064397/10000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (10001935065579161363/10000000000000000000 : ℝ)^256 ≤ (10000458224064397/10000000000000000 : ℝ)^1081 := by
      have hnat : (10001935065579161363 : ℕ)^256*10000000000000000^1081 ≤ 10000458224064397^1081*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001935065579161363 10000000000000000000 10000458224064397 10000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000458224064397/10000000000000000 : ℝ)) (X := (10001935065579161363/10000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020164598306055389/50000000000000000000 : ℝ) ≤ (10000954920062853/10000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (50020164598306055389/50000000000000000000 : ℝ)^256 ≤ (10000954920062853/10000000000000000 : ℝ)^1081 := by
      have hnat : (50020164598306055389 : ℕ)^256*10000000000000000^1081 ≤ 10000954920062853^1081*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020164598306055389 50000000000000000000 10000954920062853 10000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000954920062853/10000000000000000 : ℝ)) (X := (50020164598306055389/50000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030653868716303963/50000000000000000000 : ℝ) ≤ (10001451616061309/10000000000000000 : ℝ) ^ (1081/256 : ℝ) := by
    have hpowers : (50030653868716303963/50000000000000000000 : ℝ)^256 ≤ (10001451616061309/10000000000000000 : ℝ)^1081 := by
      have hnat : (50030653868716303963 : ℕ)^256*10000000000000000^1081 ≤ 10001451616061309^1081*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030653868716303963 50000000000000000000 10001451616061309 10000000000000000 256 1081 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001451616061309/10000000000000000 : ℝ)) (X := (50030653868716303963/50000000000000000000 : ℝ)) (by norm_num) 1081 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1935065579161363/20000000000000000000 : ℝ) ≤ ((3517048306171714351/3518000000000000000 : ℝ)+2*(62086999807/43975000000000 : ℝ)*(11203/100000 : ℝ))^(1081/256 : ℝ) := by
    rw [show (3517048306171714351/3518000000000000000 : ℝ)+2*(62086999807/43975000000000 : ℝ)*(11203/100000 : ℝ)=(10000458224064397/10000000000000000 : ℝ) by norm_num, show 1+2*(1935065579161363/20000000000000000000 : ℝ)=(10001935065579161363/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30653868716303963/100000000000000000000 : ℝ)+(1935065579161363/20000000000000000000 : ℝ) ≤ ((3517048306171714351/3518000000000000000 : ℝ)+(62086999807/43975000000000 : ℝ)*((14721/100000 : ℝ)+(11203/100000 : ℝ)))^(1081/256 : ℝ) := by
    rw [show (3517048306171714351/3518000000000000000 : ℝ)+(62086999807/43975000000000 : ℝ)*((14721/100000 : ℝ)+(11203/100000 : ℝ))=(10000954920062853/10000000000000000 : ℝ) by norm_num, show 1+(30653868716303963/100000000000000000000 : ℝ)+(1935065579161363/20000000000000000000 : ℝ)=(50020164598306055389/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30653868716303963/100000000000000000000 : ℝ) ≤ ((3517048306171714351/3518000000000000000 : ℝ)+2*(62086999807/43975000000000 : ℝ)*(14721/100000 : ℝ))^(1081/256 : ℝ) := by
    rw [show (3517048306171714351/3518000000000000000 : ℝ)+2*(62086999807/43975000000000 : ℝ)*(14721/100000 : ℝ)=(10001451616061309/10000000000000000 : ℝ) by norm_num, show 1+2*(30653868716303963/100000000000000000000 : ℝ)=(50030653868716303963/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3517048306171714351/3518000000000000000 : ℝ)*(X 1 0+X 2 0)+(62086999807/43975000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (14721/100000 : ℝ)) (c := (3517048306171714351/3518000000000000000 : ℝ)) (alpha := (62086999807/43975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3517048306171714351/3518000000000000000 : ℝ)*(X 0 1+X 2 1)+(62086999807/43975000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (14721/100000 : ℝ)) (c := (3517048306171714351/3518000000000000000 : ℝ)) (alpha := (62086999807/43975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3517048306171714351/3518000000000000000 : ℝ)*(X 0 2+X 1 2)+(62086999807/43975000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1081/256 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (14721/100000 : ℝ)) (c := (3517048306171714351/3518000000000000000 : ℝ)) (alpha := (62086999807/43975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-46470369/250000000 : ℝ)*X 0 0+(1077795373/2000000000 : ℝ)*X 0 1+(5388977411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285459663/10000000000 : ℝ)*X 1 0+(-1000374481/5000000000 : ℝ)*X 1 1+(2694488397/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642729741/5000000000 : ℝ)*X 2 0+(538897693/1000000000 : ℝ)*X 2 1+(-2000749021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4468305459/10000000000 : ℝ)*X 0 0+(531331423/1250000000 : ℝ)*X 0 1+(2125325819/5000000000 : ℝ)*X 0 2+(4468305459/10000000000 : ℝ)*X 1 0+(531331423/1250000000 : ℝ)*X 1 1+(2125325819/5000000000 : ℝ)*X 1 2+(4468305459/10000000000 : ℝ)*X 2 0+(531331423/1250000000 : ℝ)*X 2 1+(2125325819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1096233663/5000000000 : ℝ)*X 0 0+(658176599/1250000000 : ℝ)*X 0 1+(329088293/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1343041147/2500000000 : ℝ)*X 1 0+(-1025245239/5000000000 : ℝ)*X 1 1+(5265412483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1343041153/2500000000 : ℝ)*X 2 0+(658176583/1250000000 : ℝ)*X 2 1+(-512622551/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2086011291/5000000000 : ℝ)*X 0 0+(2199370081/5000000000 : ℝ)*X 0 1+(2199370031/5000000000 : ℝ)*X 0 2+(2086011291/5000000000 : ℝ)*X 1 0+(2199370081/5000000000 : ℝ)*X 1 1+(2199370031/5000000000 : ℝ)*X 1 2+(2086011291/5000000000 : ℝ)*X 2 0+(2199370081/5000000000 : ℝ)*X 2 1+(2199370031/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2122341941/10000000000 : ℝ)*X 0 0+(80941243/156250000 : ℝ)*X 0 1+(5402987003/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((329726489/625000000 : ℝ)*X 1 0+(-3896443/19531250 : ℝ)*X 1 1+(5402986521/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275623831/10000000000 : ℝ)*X 2 0+(5402986583/10000000000 : ℝ)*X 2 1+(-498744681/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4501338551/10000000000 : ℝ)*X 0 0+(4233847581/10000000000 : ℝ)*X 0 1+(2116923811/5000000000 : ℝ)*X 0 2+(4501338551/10000000000 : ℝ)*X 1 0+(4233847581/10000000000 : ℝ)*X 1 1+(2116923811/5000000000 : ℝ)*X 1 2+(4501338551/10000000000 : ℝ)*X 2 0+(4233847581/10000000000 : ℝ)*X 2 1+(2116923811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-482308409/2500000000 : ℝ)*X 0 0+(2735997737/5000000000 : ℝ)*X 0 1+(5254325289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1075988519/2000000000 : ℝ)*X 1 0+(-2054850639/10000000000 : ℝ)*X 1 1+(5254325209/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2689971227/5000000000 : ℝ)*X 2 0+(2627162693/5000000000 : ℝ)*X 2 1+(-2054850593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4144989063/10000000000 : ℝ)*X 0 0+(882403447/2000000000 : ℝ)*X 0 1+(176480687/400000000 : ℝ)*X 0 2+(4144989063/10000000000 : ℝ)*X 1 0+(882403447/2000000000 : ℝ)*X 1 1+(176480687/400000000 : ℝ)*X 1 2+(4144989063/10000000000 : ℝ)*X 2 0+(882403447/2000000000 : ℝ)*X 2 1+(176480687/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1365_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12573/20000 : ℝ) ≤ (-55287630530557548820155942528933/87950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27936411/100000000000000 : ℝ)*(upper0) + (39637193/100000000000000 : ℝ)*(lower2) + (4042903/6250000000000 : ℝ)*(upper4) + (2244901/25000000000000 : ℝ)*(upper5) + (1473137561828013/50000000000000 : ℝ)*(major0) + (1473137561828013/50000000000000 : ℝ)*(major1) + (1473137561828013/50000000000000 : ℝ)*(major2) + (5459584553/50000000000000 : ℝ)*(sp1) + (431582743/50000000000000 : ℝ)*(sp3) + (2010220436748881/50000000000000 : ℝ)*(sp4) + (2010216885327381/50000000000000 : ℝ)*(sp5) + (1005111172455967/25000000000000 : ℝ)*(sp6) + (1893058884404387/100000000000000 : ℝ)*(sp7) + (1908163053/50000000000000 : ℝ)*(sp8) + (1893059747569873/100000000000000 : ℝ)*(f.failure) + (1005111172455967/25000000000000 : ℝ)*(f.sum) + (28106946688161/4397500000000000000000000000 : ℝ)*base66 + (625687245745405437/175900000000000000000000000000000 : ℝ)*base68 + (2347569408567205437/175900000000000000000000000000000 : ℝ)*base70 + (1838246034422605437/175900000000000000000000000000000 : ℝ)*base72 + (4855517062261/4397500000000000000000000000 : ℝ)*base74 + (1646065368939605437/175900000000000000000000000000000 : ℝ)*base76 + (2006022951666405437/175900000000000000000000000000000 : ℝ)*base78 + (2217080638047805437/175900000000000000000000000000000 : ℝ)*base80 + (9352092209561/4397500000000000000000000000 : ℝ)*base82 + (24279319/2500000000000000000000 : ℝ)*base89 + (24279319/2500000000000000000000 : ℝ)*base91 + (24279319/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29493/50000 : ℝ) ≤ (10376078406093609696938180400837/17590000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (127669/12500000000000 : ℝ)*(lower0) + (4584649/4000000000000 : ℝ)*(lower1) + (2322281/100000000000000 : ℝ)*(lower3) + (5359903/4000000000000 : ℝ)*(lower5) + (603148010240871/20000000000000 : ℝ)*(major0) + (603148010240871/20000000000000 : ℝ)*(major1) + (603148010240871/20000000000000 : ℝ)*(major2) + (4074105257105707/100000000000000 : ℝ)*(sp0) + (127314046631349/3125000000000 : ℝ)*(sp1) + (4074124464610429/100000000000000 : ℝ)*(sp2) + (6055262550459/312500000000 : ℝ)*(sp3) + (549121109/6250000000000 : ℝ)*(sp7) + (74972407261/100000000000000 : ℝ)*(sp9) + (9603752361/50000000000000 : ℝ)*(sp12) + (15501542416677/800000000000 : ℝ)*(f.failure) + (4074124464610429/100000000000000 : ℝ)*(f.sum) + (1104334830961/439750000000000000000000000 : ℝ)*base65 + (31688441863960279/70360000000000000000000000000000 : ℝ)*base68 + (142147507290119721/70360000000000000000000000000000 : ℝ)*base69 + (269740964653839721/70360000000000000000000000000000 : ℝ)*base71 + (3202652939279/439750000000000000000000000 : ℝ)*base74 + (653164226900439721/70360000000000000000000000000000 : ℝ)*base75 + (328341041395039721/70360000000000000000000000000000 : ℝ)*base77 + (262535534818719721/70360000000000000000000000000000 : ℝ)*base79 + (860181973307/1759000000000000000000000000 : ℝ)*base81 + (24669/20000000000000000000 : ℝ)*base90 + (24669/20000000000000000000 : ℝ)*base92 + (24669/20000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (10011/12500 : ℝ) ≤ (35219747534638145095999394618853/43975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2918753/25000000000000 : ℝ)*(upper0) + (5779473/20000000000000 : ℝ)*(upper1) + (31493633/50000000000000 : ℝ)*(lower3) + (10476229/100000000000000 : ℝ)*(upper4) + (1663422992493601/50000000000000 : ℝ)*(major0) + (1663422992493601/50000000000000 : ℝ)*(major1) + (1663422992493601/50000000000000 : ℝ)*(major2) + (7456183951/100000000000000 : ℝ)*(sp2) + (8088689177/25000000000000 : ℝ)*(sp3) + (140293756269673/3125000000000 : ℝ)*(sp8) + (44894085756751/1000000000000 : ℝ)*(sp9) + (4489401119491149/100000000000000 : ℝ)*(sp10) + (2137554243988573/100000000000000 : ℝ)*(sp11) + (2093761391/25000000000000 : ℝ)*(sp12) + (2137586598745281/100000000000000 : ℝ)*(f.failure) + (44894085756751/1000000000000 : ℝ)*(f.sum) + (5638755898869/8795000000000000000000000000 : ℝ)*base66 + (1153107317300772049/175900000000000000000000000000000 : ℝ)*base68 + (299643971675327951/175900000000000000000000000000000 : ℝ)*base69 + (2721109486442572049/175900000000000000000000000000000 : ℝ)*base72 + (52686099522981/8795000000000000000000000000 : ℝ)*base73 + (561727509771072049/175900000000000000000000000000000 : ℝ)*base76 + (1518580183138472049/175900000000000000000000000000000 : ℝ)*base78 + (655507165055872049/175900000000000000000000000000000 : ℝ)*base80 + (7040567741971/8795000000000000000000000000 : ℝ)*base81 + (10136743/2500000000000000000000 : ℝ)*base89 + (10136743/2500000000000000000000 : ℝ)*base91 + (10136743/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84441/100000 : ℝ) ≤ (-1160374313120246596646150880567/1374218750000000000000000000000 : ℝ) := by norm_num
    linear_combination (125282637/100000000000000 : ℝ)*(lower0) + (10497509/10000000000000 : ℝ)*(lower1) + (71980867/100000000000000 : ℝ)*(lower2) + (10744899/12500000000000 : ℝ)*(lower4) + (105111684216531/3125000000000 : ℝ)*(major0) + (105111684216531/3125000000000 : ℝ)*(major1) + (105111684216531/3125000000000 : ℝ)*(major2) + (72332029/2500000000000 : ℝ)*(sp0) + (4074189137/2500000000000 : ℝ)*(sp5) + (12207381651/12500000000000 : ℝ)*(sp6) + (4594105922179333/100000000000000 : ℝ)*(sp12) + (4593945847895013/100000000000000 : ℝ)*(sp13) + (918802231281457/20000000000000 : ℝ)*(sp14) + (540296313244971/25000000000000 : ℝ)*(sp15) + (540296313244971/25000000000000 : ℝ)*(f.failure) + (4594108815460493/100000000000000 : ℝ)*(f.sum) + (981005423793/68710937500000000000000000 : ℝ)*base66 + (164654250417133881/10993750000000000000000000000000 : ℝ)*base67 + (43360935387852631/10993750000000000000000000000000 : ℝ)*base69 + (555350064423915131/10993750000000000000000000000000 : ℝ)*base71 + (7997490669741/8795000000000000000000000000 : ℝ)*base73 + (58573640731352631/10993750000000000000000000000000 : ℝ)*base75 + (394235660323891119/10993750000000000000000000000000 : ℝ)*base78 + (35554699507366119/10993750000000000000000000000000 : ℝ)*base80 + (21892488920091/8795000000000000000000000000 : ℝ)*base81 + (8123187/625000000000000000000 : ℝ)*base90 + (8123187/625000000000000000000 : ℝ)*base92 + (8123187/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1365_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12573/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29493/50000 : ℝ) else (10011/12500 : ℝ) ≤ X j i ∧ X j i ≤ (84441/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1365_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1365_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2799/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12573/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29493/50000 : ℝ) else (10011/12500 : ℝ) ≤ X j i ∧ X j i ≤ (84441/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1365_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1365_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1365_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1081/256 : ℝ) ≤ p) (hpb : p ≤ (4325/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38908903/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1841/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2799/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12573/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29493/50000 : ℝ) else (10011/12500 : ℝ) ≤ X j i ∧ X j i ≤ (84441/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1365_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

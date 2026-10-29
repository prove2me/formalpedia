-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1491_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:15:46.57199+00:00
-- url     : https://prove2.me/submissions/76047b74-18c2-4c18-8337-6cc0191abf4a

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
theorem support_rectangle_w1491_s6_0 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1899493877/10000000000 : ℝ)*x 0 + (1087195361/2000000000 : ℝ)*x 1 + (2608252263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1899493877/10000000000 : ℝ)^4479 ≤ (2322036870521/20000000000000 : ℝ)^3455 := by
    have hnat : (1899493877 : ℕ)^4479*20000000000000^3455 ≤ 2322036870521^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899493877 10000000000 2322036870521 20000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087195361/2000000000 : ℝ)^4479 ≤ (22687603774839/50000000000000 : ℝ)^3455 := by
    have hnat : (1087195361 : ℕ)^4479*50000000000000^3455 ≤ 22687603774839^3455*2000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087195361 2000000000 22687603774839 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608252263/5000000000 : ℝ)^4479 ≤ (43014608073313/100000000000000 : ℝ)^3455 := by
    have hnat : (2608252263 : ℕ)^4479*100000000000000^3455 ≤ 43014608073313^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608252263 5000000000 43014608073313 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1899493877/10000000000 : ℝ), (1087195361/2000000000 : ℝ), (2608252263/5000000000 : ℝ)] ![(2322036870521/20000000000000 : ℝ), (22687603774839/50000000000000 : ℝ), (43014608073313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1899493877/10000000000 : ℝ)|^4479 ≤ (2322036870521/20000000000000 : ℝ)^3455
        have hw : |(-1899493877/10000000000 : ℝ)|=(1899493877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087195361/2000000000 : ℝ)|^4479 ≤ (22687603774839/50000000000000 : ℝ)^3455
        have hw : |(1087195361/2000000000 : ℝ)|=(1087195361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608252263/5000000000 : ℝ)|^4479 ≤ (43014608073313/100000000000000 : ℝ)^3455
        have hw : |(2608252263/5000000000 : ℝ)|=(2608252263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s6_1 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338182991/2500000000 : ℝ)*x 0 + (-402389057/2000000000 : ℝ)*x 1 + (5216504467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338182991/2500000000 : ℝ)^4479 ≤ (44476452981769/100000000000000 : ℝ)^3455 := by
    have hnat : (1338182991 : ℕ)^4479*100000000000000^3455 ≤ 44476452981769^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338182991 2500000000 44476452981769 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402389057/2000000000 : ℝ)^4479 ≤ (6254469778951/50000000000000 : ℝ)^3455 := by
    have hnat : (402389057 : ℕ)^4479*50000000000000^3455 ≤ 6254469778951^3455*2000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402389057 2000000000 6254469778951 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216504467/10000000000 : ℝ)^4479 ≤ (8602921488523/20000000000000 : ℝ)^3455 := by
    have hnat : (5216504467 : ℕ)^4479*20000000000000^3455 ≤ 8602921488523^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216504467 10000000000 8602921488523 20000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338182991/2500000000 : ℝ), (-402389057/2000000000 : ℝ), (5216504467/10000000000 : ℝ)] ![(44476452981769/100000000000000 : ℝ), (6254469778951/50000000000000 : ℝ), (8602921488523/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338182991/2500000000 : ℝ)|^4479 ≤ (44476452981769/100000000000000 : ℝ)^3455
        have hw : |(1338182991/2500000000 : ℝ)|=(1338182991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-402389057/2000000000 : ℝ)|^4479 ≤ (6254469778951/50000000000000 : ℝ)^3455
        have hw : |(-402389057/2000000000 : ℝ)|=(402389057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216504467/10000000000 : ℝ)|^4479 ≤ (8602921488523/20000000000000 : ℝ)^3455
        have hw : |(5216504467/10000000000 : ℝ)|=(5216504467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s6_2 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669091531/1250000000 : ℝ)*x 0 + (5216504231/10000000000 : ℝ)*x 1 + (-2011945219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669091531/1250000000 : ℝ)^4479 ≤ (11119114010239/25000000000000 : ℝ)^3455 := by
    have hnat : (669091531 : ℕ)^4479*25000000000000^3455 ≤ 11119114010239^3455*1250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669091531 1250000000 11119114010239 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216504231/10000000000 : ℝ)^4479 ≤ (43014604919823/100000000000000 : ℝ)^3455 := by
    have hnat : (5216504231 : ℕ)^4479*100000000000000^3455 ≤ 43014604919823^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216504231 10000000000 43014604919823 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011945219/10000000000 : ℝ)^4479 ≤ (12508939025939/100000000000000 : ℝ)^3455 := by
    have hnat : (2011945219 : ℕ)^4479*100000000000000^3455 ≤ 12508939025939^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011945219 10000000000 12508939025939 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669091531/1250000000 : ℝ), (5216504231/10000000000 : ℝ), (-2011945219/10000000000 : ℝ)] ![(11119114010239/25000000000000 : ℝ), (43014604919823/100000000000000 : ℝ), (12508939025939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669091531/1250000000 : ℝ)|^4479 ≤ (11119114010239/25000000000000 : ℝ)^3455
        have hw : |(669091531/1250000000 : ℝ)|=(669091531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216504231/10000000000 : ℝ)|^4479 ≤ (43014604919823/100000000000000 : ℝ)^3455
        have hw : |(5216504231/10000000000 : ℝ)|=(5216504231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011945219/10000000000 : ℝ)|^4479 ≤ (12508939025939/100000000000000 : ℝ)^3455
        have hw : |(-2011945219/10000000000 : ℝ)|=(2011945219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s6_3 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34237219/80000000 : ℝ)*x 0 + (2020281231/5000000000 : ℝ)*x 1 + (1132719833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34237219/80000000 : ℝ)^4479 ≤ (4159820576277/12500000000000 : ℝ)^3455 := by
    have hnat : (34237219 : ℕ)^4479*12500000000000^3455 ≤ 4159820576277^3455*80000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34237219 80000000 4159820576277 12500000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2020281231/5000000000 : ℝ)^4479 ≤ (30888601376997/100000000000000 : ℝ)^3455 := by
    have hnat : (2020281231 : ℕ)^4479*100000000000000^3455 ≤ 30888601376997^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020281231 5000000000 30888601376997 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132719833/2500000000 : ℝ)^4479 ≤ (8958208500751/25000000000000 : ℝ)^3455 := by
    have hnat : (1132719833 : ℕ)^4479*25000000000000^3455 ≤ 8958208500751^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132719833 2500000000 8958208500751 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34237219/80000000 : ℝ), (2020281231/5000000000 : ℝ), (1132719833/2500000000 : ℝ)] ![(4159820576277/12500000000000 : ℝ), (30888601376997/100000000000000 : ℝ), (8958208500751/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34237219/80000000 : ℝ)|^4479 ≤ (4159820576277/12500000000000 : ℝ)^3455
        have hw : |(34237219/80000000 : ℝ)|=(34237219/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2020281231/5000000000 : ℝ)|^4479 ≤ (30888601376997/100000000000000 : ℝ)^3455
        have hw : |(2020281231/5000000000 : ℝ)|=(2020281231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132719833/2500000000 : ℝ)|^4479 ≤ (8958208500751/25000000000000 : ℝ)^3455
        have hw : |(1132719833/2500000000 : ℝ)|=(1132719833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s6_4 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-474880867/2500000000 : ℝ)*x 0 + (5217629733/10000000000 : ℝ)*x 1 + (5434843521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (474880867/2500000000 : ℝ)^4479 ≤ (5805209413351/50000000000000 : ℝ)^3455 := by
    have hnat : (474880867 : ℕ)^4479*50000000000000^3455 ≤ 5805209413351^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474880867 2500000000 5805209413351 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217629733/10000000000 : ℝ)^4479 ≤ (10756659172593/25000000000000 : ℝ)^3455 := by
    have hnat : (5217629733 : ℕ)^4479*25000000000000^3455 ≤ 10756659172593^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217629733 10000000000 10756659172593 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434843521/10000000000 : ℝ)^4479 ≤ (22681472237409/50000000000000 : ℝ)^3455 := by
    have hnat : (5434843521 : ℕ)^4479*50000000000000^3455 ≤ 22681472237409^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434843521 10000000000 22681472237409 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-474880867/2500000000 : ℝ), (5217629733/10000000000 : ℝ), (5434843521/10000000000 : ℝ)] ![(5805209413351/50000000000000 : ℝ), (10756659172593/25000000000000 : ℝ), (22681472237409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-474880867/2500000000 : ℝ)|^4479 ≤ (5805209413351/50000000000000 : ℝ)^3455
        have hw : |(-474880867/2500000000 : ℝ)|=(474880867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217629733/10000000000 : ℝ)|^4479 ≤ (10756659172593/25000000000000 : ℝ)^3455
        have hw : |(5217629733/10000000000 : ℝ)|=(5217629733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434843521/10000000000 : ℝ)|^4479 ≤ (22681472237409/50000000000000 : ℝ)^3455
        have hw : |(5434843521/10000000000 : ℝ)|=(5434843521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s6_5 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295307737/10000000000 : ℝ)*x 0 + (-224200833/1250000000 : ℝ)*x 1 + (5434843541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295307737/10000000000 : ℝ)^4479 ≤ (43858877452631/100000000000000 : ℝ)^3455 := by
    have hnat : (5295307737 : ℕ)^4479*100000000000000^3455 ≤ 43858877452631^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295307737 10000000000 43858877452631 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224200833/1250000000 : ℝ)^4479 ≤ (1347272230713/12500000000000 : ℝ)^3455 := by
    have hnat : (224200833 : ℕ)^4479*12500000000000^3455 ≤ 1347272230713^3455*1250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224200833 1250000000 1347272230713 12500000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434843541/10000000000 : ℝ)^4479 ≤ (11340736172807/25000000000000 : ℝ)^3455 := by
    have hnat : (5434843541 : ℕ)^4479*25000000000000^3455 ≤ 11340736172807^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434843541 10000000000 11340736172807 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295307737/10000000000 : ℝ), (-224200833/1250000000 : ℝ), (5434843541/10000000000 : ℝ)] ![(43858877452631/100000000000000 : ℝ), (1347272230713/12500000000000 : ℝ), (11340736172807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295307737/10000000000 : ℝ)|^4479 ≤ (43858877452631/100000000000000 : ℝ)^3455
        have hw : |(5295307737/10000000000 : ℝ)|=(5295307737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-224200833/1250000000 : ℝ)|^4479 ≤ (1347272230713/12500000000000 : ℝ)^3455
        have hw : |(-224200833/1250000000 : ℝ)|=(224200833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434843541/10000000000 : ℝ)|^4479 ≤ (11340736172807/25000000000000 : ℝ)^3455
        have hw : |(5434843541/10000000000 : ℝ)|=(5434843541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s6_6 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295307743/10000000000 : ℝ)*x 0 + (5434843541/10000000000 : ℝ)*x 1 + (-1751569/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295307743/10000000000 : ℝ)^4479 ≤ (171323740301/390625000000 : ℝ)^3455 := by
    have hnat : (5295307743 : ℕ)^4479*390625000000^3455 ≤ 171323740301^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295307743 10000000000 171323740301 390625000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434843541/10000000000 : ℝ)^4479 ≤ (11340736172807/25000000000000 : ℝ)^3455 := by
    have hnat : (5434843541 : ℕ)^4479*25000000000000^3455 ≤ 11340736172807^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434843541 10000000000 11340736172807 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1751569/9765625 : ℝ)^4479 ≤ (5389088891691/50000000000000 : ℝ)^3455 := by
    have hnat : (1751569 : ℕ)^4479*50000000000000^3455 ≤ 5389088891691^3455*9765625^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1751569 9765625 5389088891691 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295307743/10000000000 : ℝ), (5434843541/10000000000 : ℝ), (-1751569/9765625 : ℝ)] ![(171323740301/390625000000 : ℝ), (11340736172807/25000000000000 : ℝ), (5389088891691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295307743/10000000000 : ℝ)|^4479 ≤ (171323740301/390625000000 : ℝ)^3455
        have hw : |(5295307743/10000000000 : ℝ)|=(5295307743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434843541/10000000000 : ℝ)|^4479 ≤ (11340736172807/25000000000000 : ℝ)^3455
        have hw : |(5434843541/10000000000 : ℝ)|=(5434843541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1751569/9765625 : ℝ)|^4479 ≤ (5389088891691/50000000000000 : ℝ)^3455
        have hw : |(-1751569/9765625 : ℝ)|=(1751569/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_s6_7 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (427971991/1000000000 : ℝ)*x 0 + (4528365273/10000000000 : ℝ)*x 1 + (4043094181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427971991/1000000000 : ℝ)^4479 ≤ (16639622704697/50000000000000 : ℝ)^3455 := by
    have hnat : (427971991 : ℕ)^4479*50000000000000^3455 ≤ 16639622704697^3455*1000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427971991 1000000000 16639622704697 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4528365273/10000000000 : ℝ)^4479 ≤ (35807060620393/100000000000000 : ℝ)^3455 := by
    have hnat : (4528365273 : ℕ)^4479*100000000000000^3455 ≤ 35807060620393^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528365273 10000000000 35807060620393 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4043094181/10000000000 : ℝ)^4479 ≤ (30913693953021/100000000000000 : ℝ)^3455 := by
    have hnat : (4043094181 : ℕ)^4479*100000000000000^3455 ≤ 30913693953021^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4043094181 10000000000 30913693953021 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(427971991/1000000000 : ℝ), (4528365273/10000000000 : ℝ), (4043094181/10000000000 : ℝ)] ![(16639622704697/50000000000000 : ℝ), (35807060620393/100000000000000 : ℝ), (30913693953021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(427971991/1000000000 : ℝ)|^4479 ≤ (16639622704697/50000000000000 : ℝ)^3455
        have hw : |(427971991/1000000000 : ℝ)|=(427971991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4528365273/10000000000 : ℝ)|^4479 ≤ (35807060620393/100000000000000 : ℝ)^3455
        have hw : |(4528365273/10000000000 : ℝ)|=(4528365273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4043094181/10000000000 : ℝ)|^4479 ≤ (30913693953021/100000000000000 : ℝ)^3455
        have hw : |(4043094181/10000000000 : ℝ)|=(4043094181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1491_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10831/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (677/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7739/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10831/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10831/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10831/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10831/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10831/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10831/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10831/100000 : ℝ) ^ (4477/1024 : ℝ) ≤ (240748196588133/4000000000000000000 : ℝ) := by
    have hpowers : (10831/100000 : ℝ)^4477 ≤ (240748196588133/4000000000000000000 : ℝ)^1024 := by
      have hnat : (10831 : ℕ)^4477*4000000000000000000^1024 ≤ 240748196588133^1024*100000^4477 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10831 100000 240748196588133 4000000000000000000 4477 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10831/100000 : ℝ)) (X := (240748196588133/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15479/100000 : ℝ) ^ (4477/1024 : ℝ) ≤ (14337353490319983/50000000000000000000 : ℝ) := by
    have hpowers : (15479/100000 : ℝ)^4477 ≤ (14337353490319983/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15479 : ℕ)^4477*50000000000000000000^1024 ≤ 14337353490319983^1024*100000^4477 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15479 100000 14337353490319983 50000000000000000000 4477 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15479/100000 : ℝ)) (X := (14337353490319983/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000240748196588133/2000000000000000000 : ℝ) ≤ (156254301756027/156250000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (2000240748196588133/2000000000000000000 : ℝ)^1024 ≤ (156254301756027/156250000000000 : ℝ)^4477 := by
      have hnat : (2000240748196588133 : ℕ)^1024*156250000000000^4477 ≤ 156254301756027^4477*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000240748196588133 2000000000000000000 156254301756027 156250000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156254301756027/156250000000000 : ℝ)) (X := (2000240748196588133/2000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034693411895343291/100000000000000000000 : ℝ) ≤ (2000158683500971/2000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (100034693411895343291/100000000000000000000 : ℝ)^1024 ≤ (2000158683500971/2000000000000000 : ℝ)^4477 := by
      have hnat : (100034693411895343291 : ℕ)^1024*2000000000000000^4477 ≤ 2000158683500971^4477*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034693411895343291 100000000000000000000 2000158683500971 2000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000158683500971/2000000000000000 : ℝ)) (X := (100034693411895343291/100000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014337353490319983/25000000000000000000 : ℝ) ≤ (5000655761311991/5000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (25014337353490319983/25000000000000000000 : ℝ)^1024 ≤ (5000655761311991/5000000000000000 : ℝ)^4477 := by
      have hnat : (25014337353490319983 : ℕ)^1024*5000000000000000^4477 ≤ 5000655761311991^4477*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014337353490319983 25000000000000000000 5000655761311991 5000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000655761311991/5000000000000000 : ℝ)) (X := (25014337353490319983/25000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(240748196588133/4000000000000000000 : ℝ) ≤ ((4647005645887833467/4648000000000000000 : ℝ)+2*(518105119127/464800000000000 : ℝ)*(10831/100000 : ℝ))^(4477/1024 : ℝ) := by
    rw [show (4647005645887833467/4648000000000000000 : ℝ)+2*(518105119127/464800000000000 : ℝ)*(10831/100000 : ℝ)=(156254301756027/156250000000000 : ℝ) by norm_num, show 1+2*(240748196588133/4000000000000000000 : ℝ)=(2000240748196588133/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14337353490319983/50000000000000000000 : ℝ)+(240748196588133/4000000000000000000 : ℝ) ≤ ((4647005645887833467/4648000000000000000 : ℝ)+(518105119127/464800000000000 : ℝ)*((15479/100000 : ℝ)+(10831/100000 : ℝ)))^(4477/1024 : ℝ) := by
    rw [show (4647005645887833467/4648000000000000000 : ℝ)+(518105119127/464800000000000 : ℝ)*((15479/100000 : ℝ)+(10831/100000 : ℝ))=(2000158683500971/2000000000000000 : ℝ) by norm_num, show 1+(14337353490319983/50000000000000000000 : ℝ)+(240748196588133/4000000000000000000 : ℝ)=(100034693411895343291/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14337353490319983/50000000000000000000 : ℝ) ≤ ((4647005645887833467/4648000000000000000 : ℝ)+2*(518105119127/464800000000000 : ℝ)*(15479/100000 : ℝ))^(4477/1024 : ℝ) := by
    rw [show (4647005645887833467/4648000000000000000 : ℝ)+2*(518105119127/464800000000000 : ℝ)*(15479/100000 : ℝ)=(5000655761311991/5000000000000000 : ℝ) by norm_num, show 1+2*(14337353490319983/50000000000000000000 : ℝ)=(25014337353490319983/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4647005645887833467/4648000000000000000 : ℝ)*(X 1 0+X 2 0)+(518105119127/464800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (10831/100000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (4647005645887833467/4648000000000000000 : ℝ)) (alpha := (518105119127/464800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4647005645887833467/4648000000000000000 : ℝ)*(X 0 1+X 2 1)+(518105119127/464800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (10831/100000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (4647005645887833467/4648000000000000000 : ℝ)) (alpha := (518105119127/464800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4647005645887833467/4648000000000000000 : ℝ)*(X 0 2+X 1 2)+(518105119127/464800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (10831/100000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (4647005645887833467/4648000000000000000 : ℝ)) (alpha := (518105119127/464800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1899493877/10000000000 : ℝ)*X 0 0+(1087195361/2000000000 : ℝ)*X 0 1+(2608252263/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338182991/2500000000 : ℝ)*X 1 0+(-402389057/2000000000 : ℝ)*X 1 1+(5216504467/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669091531/1250000000 : ℝ)*X 2 0+(5216504231/10000000000 : ℝ)*X 2 1+(-2011945219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34237219/80000000 : ℝ)*X 0 0+(2020281231/5000000000 : ℝ)*X 0 1+(1132719833/2500000000 : ℝ)*X 0 2+(34237219/80000000 : ℝ)*X 1 0+(2020281231/5000000000 : ℝ)*X 1 1+(1132719833/2500000000 : ℝ)*X 1 2+(34237219/80000000 : ℝ)*X 2 0+(2020281231/5000000000 : ℝ)*X 2 1+(1132719833/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-474880867/2500000000 : ℝ)*X 0 0+(5217629733/10000000000 : ℝ)*X 0 1+(5434843521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295307737/10000000000 : ℝ)*X 1 0+(-224200833/1250000000 : ℝ)*X 1 1+(5434843541/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295307743/10000000000 : ℝ)*X 2 0+(5434843541/10000000000 : ℝ)*X 2 1+(-1751569/9765625 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((427971991/1000000000 : ℝ)*X 0 0+(4528365273/10000000000 : ℝ)*X 0 1+(4043094181/10000000000 : ℝ)*X 0 2+(427971991/1000000000 : ℝ)*X 1 0+(4528365273/10000000000 : ℝ)*X 1 1+(4043094181/10000000000 : ℝ)*X 1 2+(427971991/1000000000 : ℝ)*X 2 0+(4528365273/10000000000 : ℝ)*X 2 1+(4043094181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (353111985559970433440076411/58100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1041192081/50000000000000 : ℝ)*(base19) + (15139933/800000000000 : ℝ)*(base23) + (2331459/50000000000000 : ℝ)*(upper2) + (101002223/50000000000000 : ℝ)*(upper3) + (58927637/25000000000000 : ℝ)*(upper4) + (1648996056372989/50000000000000 : ℝ)*(major0) + (1648996056372989/50000000000000 : ℝ)*(major1) + (1648996056372989/50000000000000 : ℝ)*(major2) + (227820951600251/5000000000000 : ℝ)*(sp0) + (4556452088557419/100000000000000 : ℝ)*(sp1) + (4556452278449957/100000000000000 : ℝ)*(sp2) + (2039511573751009/100000000000000 : ℝ)*(sp3) + (35138936561/100000000000000 : ℝ)*(sp4) + (2284776341/12500000000000 : ℝ)*(sp7) + (2039529851961737/100000000000000 : ℝ)*(f.failure) + (4556454170941581/100000000000000 : ℝ)*(f.sum) + (20248835531937/11620000000000000000000000000 : ℝ)*base66 + (1508598609109052863/232400000000000000000000000000000 : ℝ)*base67 + (201671798028252863/232400000000000000000000000000000 : ℝ)*base69 + (1415701460294652863/232400000000000000000000000000000 : ℝ)*base71 + (5441919458337/11620000000000000000000000000 : ℝ)*base74 + (3284713700175452863/232400000000000000000000000000000 : ℝ)*base75 + (263584869886652863/232400000000000000000000000000000 : ℝ)*base77 + (1460157717320547137/232400000000000000000000000000000 : ℝ)*base80 + (40318892629657/11620000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (18818861/10000000000000000000000 : ℝ)*base90 + (18818861/10000000000000000000000 : ℝ)*base92 + (18818861/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22398948465548656187032587/3320000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1060575367/100000000000000 : ℝ)*(base19) + (1192636353/100000000000000 : ℝ)*(base23) + (350753141/100000000000000 : ℝ)*(lower1) + (28524717/20000000000000 : ℝ)*(upper3) + (27464921/50000000000000 : ℝ)*(lower4) + (129187201/100000000000000 : ℝ)*(upper5) + (333221931464509/10000000000000 : ℝ)*(major0) + (333221931464509/10000000000000 : ℝ)*(major1) + (333221931464509/10000000000000 : ℝ)*(major2) + (2131194907/100000000000000 : ℝ)*(sp2) + (1150935479000611/25000000000000 : ℝ)*(sp4) + (2301870427713539/50000000000000 : ℝ)*(sp5) + (920747718434237/20000000000000 : ℝ)*(sp6) + (515174122099667/25000000000000 : ℝ)*(sp7) + (515174122099667/25000000000000 : ℝ)*(f.failure) + (1150935479000611/25000000000000 : ℝ)*(f.sum) + (4505442783131/2324000000000000000000000000 : ℝ)*base65 + (156112529081672703/46480000000000000000000000000000 : ℝ)*base67 + (419802206414007297/46480000000000000000000000000000 : ℝ)*base70 + (4971316959677672703/46480000000000000000000000000000 : ℝ)*base71 + (180609288463/464800000000000000000000000 : ℝ)*base73 + (3704601342797527297/46480000000000000000000000000000 : ℝ)*base76 + (420899601026727297/46480000000000000000000000000000 : ℝ)*base78 + (1103479209890327297/46480000000000000000000000000000 : ℝ)*base80 + (1107708705183/2324000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8581151/2500000000000000000000 : ℝ)*base90 + (8581151/2500000000000000000000 : ℝ)*base92 + (8581151/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1491_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10831/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (677/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1491_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1491_box_0 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-420507907/2500000000 : ℝ)*x 0 + (5405107077/10000000000 : ℝ)*x 1 + (1351276793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420507907/2500000000 : ℝ)^4479 ≤ (9917113747697/100000000000000 : ℝ)^3455 := by
    have hnat : (420507907 : ℕ)^4479*100000000000000^3455 ≤ 9917113747697^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420507907 2500000000 9917113747697 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405107077/10000000000 : ℝ)^4479 ≤ (5630180325437/12500000000000 : ℝ)^3455 := by
    have hnat : (5405107077 : ℕ)^4479*12500000000000^3455 ≤ 5630180325437^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405107077 10000000000 5630180325437 12500000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351276793/2500000000 : ℝ)^4479 ≤ (45041443629773/100000000000000 : ℝ)^3455 := by
    have hnat : (1351276793 : ℕ)^4479*100000000000000^3455 ≤ 45041443629773^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351276793 2500000000 45041443629773 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-420507907/2500000000 : ℝ), (5405107077/10000000000 : ℝ), (1351276793/2500000000 : ℝ)] ![(9917113747697/100000000000000 : ℝ), (5630180325437/12500000000000 : ℝ), (45041443629773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-420507907/2500000000 : ℝ)|^4479 ≤ (9917113747697/100000000000000 : ℝ)^3455
        have hw : |(-420507907/2500000000 : ℝ)|=(420507907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405107077/10000000000 : ℝ)|^4479 ≤ (5630180325437/12500000000000 : ℝ)^3455
        have hw : |(5405107077/10000000000 : ℝ)|=(5405107077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351276793/2500000000 : ℝ)|^4479 ≤ (45041443629773/100000000000000 : ℝ)^3455
        have hw : |(1351276793/2500000000 : ℝ)|=(1351276793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_box_1 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635225163/5000000000 : ℝ)*x 0 + (-373730699/2000000000 : ℝ)*x 1 + (2702553399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635225163/5000000000 : ℝ)^4479 ≤ (2724509953009/6250000000000 : ℝ)^3455 := by
    have hnat : (2635225163 : ℕ)^4479*6250000000000^3455 ≤ 2724509953009^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635225163 5000000000 2724509953009 6250000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (373730699/2000000000 : ℝ)^4479 ≤ (11366401154823/100000000000000 : ℝ)^3455 := by
    have hnat : (373730699 : ℕ)^4479*100000000000000^3455 ≤ 11366401154823^3455*2000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373730699 2000000000 11366401154823 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702553399/5000000000 : ℝ)^4479 ≤ (45041439589483/100000000000000 : ℝ)^3455 := by
    have hnat : (2702553399 : ℕ)^4479*100000000000000^3455 ≤ 45041439589483^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702553399 5000000000 45041439589483 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635225163/5000000000 : ℝ), (-373730699/2000000000 : ℝ), (2702553399/5000000000 : ℝ)] ![(2724509953009/6250000000000 : ℝ), (11366401154823/100000000000000 : ℝ), (45041439589483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635225163/5000000000 : ℝ)|^4479 ≤ (2724509953009/6250000000000 : ℝ)^3455
        have hw : |(2635225163/5000000000 : ℝ)|=(2635225163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-373730699/2000000000 : ℝ)|^4479 ≤ (11366401154823/100000000000000 : ℝ)^3455
        have hw : |(-373730699/2000000000 : ℝ)|=(373730699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702553399/5000000000 : ℝ)|^4479 ≤ (45041439589483/100000000000000 : ℝ)^3455
        have hw : |(2702553399/5000000000 : ℝ)|=(2702553399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_box_2 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270449601/10000000000 : ℝ)*x 0 + (5405107289/10000000000 : ℝ)*x 1 + (-116790863/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270449601/10000000000 : ℝ)^4479 ≤ (69747442359/160000000000 : ℝ)^3455 := by
    have hnat : (5270449601 : ℕ)^4479*160000000000^3455 ≤ 69747442359^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270449601 10000000000 69747442359 160000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405107289/10000000000 : ℝ)^4479 ≤ (22520722446857/50000000000000 : ℝ)^3455 := by
    have hnat : (5405107289 : ℕ)^4479*50000000000000^3455 ≤ 22520722446857^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405107289 10000000000 22520722446857 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116790863/625000000 : ℝ)^4479 ≤ (11366403622973/100000000000000 : ℝ)^3455 := by
    have hnat : (116790863 : ℕ)^4479*100000000000000^3455 ≤ 11366403622973^3455*625000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116790863 625000000 11366403622973 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270449601/10000000000 : ℝ), (5405107289/10000000000 : ℝ), (-116790863/625000000 : ℝ)] ![(69747442359/160000000000 : ℝ), (22520722446857/50000000000000 : ℝ), (11366403622973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270449601/10000000000 : ℝ)|^4479 ≤ (69747442359/160000000000 : ℝ)^3455
        have hw : |(5270449601/10000000000 : ℝ)|=(5270449601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405107289/10000000000 : ℝ)|^4479 ≤ (22520722446857/50000000000000 : ℝ)^3455
        have hw : |(5405107289/10000000000 : ℝ)|=(5405107289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-116790863/625000000 : ℝ)|^4479 ≤ (11366403622973/100000000000000 : ℝ)^3455
        have hw : |(-116790863/625000000 : ℝ)|=(116790863/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_box_3 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4483707563/10000000000 : ℝ)*x 0 + (4184748347/10000000000 : ℝ)*x 1 + (2092373657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4483707563/10000000000 : ℝ)^4479 ≤ (35349951327777/100000000000000 : ℝ)^3455 := by
    have hnat : (4483707563 : ℕ)^4479*100000000000000^3455 ≤ 35349951327777^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483707563 10000000000 35349951327777 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4184748347/10000000000 : ℝ)^4479 ≤ (32325029503077/100000000000000 : ℝ)^3455 := by
    have hnat : (4184748347 : ℕ)^4479*100000000000000^3455 ≤ 32325029503077^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4184748347 10000000000 32325029503077 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2092373657/5000000000 : ℝ)^4479 ≤ (16162509579367/50000000000000 : ℝ)^3455 := by
    have hnat : (2092373657 : ℕ)^4479*50000000000000^3455 ≤ 16162509579367^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092373657 5000000000 16162509579367 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4483707563/10000000000 : ℝ), (4184748347/10000000000 : ℝ), (2092373657/5000000000 : ℝ)] ![(35349951327777/100000000000000 : ℝ), (32325029503077/100000000000000 : ℝ), (16162509579367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4483707563/10000000000 : ℝ)|^4479 ≤ (35349951327777/100000000000000 : ℝ)^3455
        have hw : |(4483707563/10000000000 : ℝ)|=(4483707563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4184748347/10000000000 : ℝ)|^4479 ≤ (32325029503077/100000000000000 : ℝ)^3455
        have hw : |(4184748347/10000000000 : ℝ)|=(4184748347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2092373657/5000000000 : ℝ)|^4479 ≤ (16162509579367/50000000000000 : ℝ)^3455
        have hw : |(2092373657/5000000000 : ℝ)|=(2092373657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_box_4 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-84896501/400000000 : ℝ)*x 0 + (1310719987/2500000000 : ℝ)*x 1 + (5242880183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84896501/400000000 : ℝ)^4479 ≤ (13406463576831/100000000000000 : ℝ)^3455 := by
    have hnat : (84896501 : ℕ)^4479*100000000000000^3455 ≤ 13406463576831^3455*400000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84896501 400000000 13406463576831 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310719987/2500000000 : ℝ)^4479 ≤ (21648383472217/50000000000000 : ℝ)^3455 := by
    have hnat : (1310719987 : ℕ)^4479*50000000000000^3455 ≤ 21648383472217^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310719987 2500000000 21648383472217 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242880183/10000000000 : ℝ)^4479 ≤ (43296769460293/100000000000000 : ℝ)^3455 := by
    have hnat : (5242880183 : ℕ)^4479*100000000000000^3455 ≤ 43296769460293^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242880183 10000000000 43296769460293 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84896501/400000000 : ℝ), (1310719987/2500000000 : ℝ), (5242880183/10000000000 : ℝ)] ![(13406463576831/100000000000000 : ℝ), (21648383472217/50000000000000 : ℝ), (43296769460293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84896501/400000000 : ℝ)|^4479 ≤ (13406463576831/100000000000000 : ℝ)^3455
        have hw : |(-84896501/400000000 : ℝ)|=(84896501/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310719987/2500000000 : ℝ)|^4479 ≤ (21648383472217/50000000000000 : ℝ)^3455
        have hw : |(1310719987/2500000000 : ℝ)|=(1310719987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242880183/10000000000 : ℝ)|^4479 ≤ (43296769460293/100000000000000 : ℝ)^3455
        have hw : |(5242880183/10000000000 : ℝ)|=(5242880183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_box_5 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383580781/10000000000 : ℝ)*x 0 + (-1935237673/10000000000 : ℝ)*x 1 + (1310720033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383580781/10000000000 : ℝ)^4479 ≤ (44809033208861/100000000000000 : ℝ)^3455 := by
    have hnat : (5383580781 : ℕ)^4479*100000000000000^3455 ≤ 44809033208861^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383580781 10000000000 44809033208861 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1935237673/10000000000 : ℝ)^4479 ≤ (2973549465353/25000000000000 : ℝ)^3455 := by
    have hnat : (1935237673 : ℕ)^4479*25000000000000^3455 ≤ 2973549465353^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935237673 10000000000 2973549465353 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310720033/2500000000 : ℝ)^4479 ≤ (21648384457149/50000000000000 : ℝ)^3455 := by
    have hnat : (1310720033 : ℕ)^4479*50000000000000^3455 ≤ 21648384457149^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310720033 2500000000 21648384457149 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383580781/10000000000 : ℝ), (-1935237673/10000000000 : ℝ), (1310720033/2500000000 : ℝ)] ![(44809033208861/100000000000000 : ℝ), (2973549465353/25000000000000 : ℝ), (21648384457149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383580781/10000000000 : ℝ)|^4479 ≤ (44809033208861/100000000000000 : ℝ)^3455
        have hw : |(5383580781/10000000000 : ℝ)|=(5383580781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1935237673/10000000000 : ℝ)|^4479 ≤ (2973549465353/25000000000000 : ℝ)^3455
        have hw : |(-1935237673/10000000000 : ℝ)|=(1935237673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310720033/2500000000 : ℝ)|^4479 ≤ (21648384457149/50000000000000 : ℝ)^3455
        have hw : |(1310720033/2500000000 : ℝ)|=(1310720033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_box_6 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076716081/2000000000 : ℝ)*x 0 + (5242880321/10000000000 : ℝ)*x 1 + (-241904741/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076716081/2000000000 : ℝ)^4479 ≤ (22404514575883/50000000000000 : ℝ)^3455 := by
    have hnat : (1076716081 : ℕ)^4479*50000000000000^3455 ≤ 22404514575883^3455*2000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076716081 2000000000 22404514575883 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242880321/10000000000 : ℝ)^4479 ≤ (10824192734423/25000000000000 : ℝ)^3455 := by
    have hnat : (5242880321 : ℕ)^4479*25000000000000^3455 ≤ 10824192734423^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242880321 10000000000 10824192734423 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241904741/1250000000 : ℝ)^4479 ≤ (594709994659/5000000000000 : ℝ)^3455 := by
    have hnat : (241904741 : ℕ)^4479*5000000000000^3455 ≤ 594709994659^3455*1250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241904741 1250000000 594709994659 5000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076716081/2000000000 : ℝ), (5242880321/10000000000 : ℝ), (-241904741/1250000000 : ℝ)] ![(22404514575883/50000000000000 : ℝ), (10824192734423/25000000000000 : ℝ), (594709994659/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076716081/2000000000 : ℝ)|^4479 ≤ (22404514575883/50000000000000 : ℝ)^3455
        have hw : |(1076716081/2000000000 : ℝ)|=(1076716081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242880321/10000000000 : ℝ)|^4479 ≤ (10824192734423/25000000000000 : ℝ)^3455
        have hw : |(5242880321/10000000000 : ℝ)|=(5242880321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-241904741/1250000000 : ℝ)|^4479 ≤ (594709994659/5000000000000 : ℝ)^3455
        have hw : |(-241904741/1250000000 : ℝ)|=(241904741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_box_7 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4073283559/10000000000 : ℝ)*x 0 + (877964561/2000000000 : ℝ)*x 1 + (548727829/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4073283559/10000000000 : ℝ)^4479 ≤ (1950829228001/6250000000000 : ℝ)^3455 := by
    have hnat : (4073283559 : ℕ)^4479*6250000000000^3455 ≤ 1950829228001^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4073283559 10000000000 1950829228001 6250000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (877964561/2000000000 : ℝ)^4479 ≤ (8598341761967/25000000000000 : ℝ)^3455 := by
    have hnat : (877964561 : ℕ)^4479*25000000000000^3455 ≤ 8598341761967^3455*2000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877964561 2000000000 8598341761967 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548727829/1250000000 : ℝ)^4479 ≤ (17196682645363/50000000000000 : ℝ)^3455 := by
    have hnat : (548727829 : ℕ)^4479*50000000000000^3455 ≤ 17196682645363^3455*1250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548727829 1250000000 17196682645363 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4073283559/10000000000 : ℝ), (877964561/2000000000 : ℝ), (548727829/1250000000 : ℝ)] ![(1950829228001/6250000000000 : ℝ), (8598341761967/25000000000000 : ℝ), (17196682645363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4073283559/10000000000 : ℝ)|^4479 ≤ (1950829228001/6250000000000 : ℝ)^3455
        have hw : |(4073283559/10000000000 : ℝ)|=(4073283559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(877964561/2000000000 : ℝ)|^4479 ≤ (8598341761967/25000000000000 : ℝ)^3455
        have hw : |(877964561/2000000000 : ℝ)|=(877964561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548727829/1250000000 : ℝ)|^4479 ≤ (17196682645363/50000000000000 : ℝ)^3455
        have hw : |(548727829/1250000000 : ℝ)|=(548727829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_box_8 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2029466809/10000000000 : ℝ)*x 0 + (128236593/250000000 : ℝ)*x 1 + (54256217/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2029466809/10000000000 : ℝ)^4479 ≤ (12650345675519/100000000000000 : ℝ)^3455 := by
    have hnat : (2029466809 : ℕ)^4479*100000000000000^3455 ≤ 12650345675519^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029466809 10000000000 12650345675519 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128236593/250000000 : ℝ)^4479 ≤ (42086469422093/100000000000000 : ℝ)^3455 := by
    have hnat : (128236593 : ℕ)^4479*100000000000000^3455 ≤ 42086469422093^3455*250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128236593 250000000 42086469422093 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54256217/100000000 : ℝ)^4479 ≤ (45263184890617/100000000000000 : ℝ)^3455 := by
    have hnat : (54256217 : ℕ)^4479*100000000000000^3455 ≤ 45263184890617^3455*100000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54256217 100000000 45263184890617 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2029466809/10000000000 : ℝ), (128236593/250000000 : ℝ), (54256217/100000000 : ℝ)] ![(12650345675519/100000000000000 : ℝ), (42086469422093/100000000000000 : ℝ), (45263184890617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2029466809/10000000000 : ℝ)|^4479 ≤ (12650345675519/100000000000000 : ℝ)^3455
        have hw : |(-2029466809/10000000000 : ℝ)|=(2029466809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(128236593/250000000 : ℝ)|^4479 ≤ (42086469422093/100000000000000 : ℝ)^3455
        have hw : |(128236593/250000000 : ℝ)|=(128236593/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54256217/100000000 : ℝ)|^4479 ≤ (45263184890617/100000000000000 : ℝ)^3455
        have hw : |(54256217/100000000 : ℝ)|=(54256217/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_box_9 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051227379/2000000000 : ℝ)*x 0 + (-929991059/5000000000 : ℝ)*x 1 + (2712810783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051227379/2000000000 : ℝ)^4479 ≤ (10859686533521/25000000000000 : ℝ)^3455 := by
    have hnat : (1051227379 : ℕ)^4479*25000000000000^3455 ≤ 10859686533521^3455*2000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051227379 2000000000 10859686533521 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (929991059/5000000000 : ℝ)^4479 ≤ (1412258800353/12500000000000 : ℝ)^3455 := by
    have hnat : (929991059 : ℕ)^4479*12500000000000^3455 ≤ 1412258800353^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929991059 5000000000 1412258800353 12500000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712810783/5000000000 : ℝ)^4479 ≤ (226315917207/500000000000 : ℝ)^3455 := by
    have hnat : (2712810783 : ℕ)^4479*500000000000^3455 ≤ 226315917207^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712810783 5000000000 226315917207 500000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051227379/2000000000 : ℝ), (-929991059/5000000000 : ℝ), (2712810783/5000000000 : ℝ)] ![(10859686533521/25000000000000 : ℝ), (1412258800353/12500000000000 : ℝ), (226315917207/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051227379/2000000000 : ℝ)|^4479 ≤ (10859686533521/25000000000000 : ℝ)^3455
        have hw : |(1051227379/2000000000 : ℝ)|=(1051227379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-929991059/5000000000 : ℝ)|^4479 ≤ (1412258800353/12500000000000 : ℝ)^3455
        have hw : |(-929991059/5000000000 : ℝ)|=(929991059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712810783/5000000000 : ℝ)|^4479 ≤ (226315917207/500000000000 : ℝ)^3455
        have hw : |(2712810783/5000000000 : ℝ)|=(2712810783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_box_10 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628068279/5000000000 : ℝ)*x 0 + (5425621939/10000000000 : ℝ)*x 1 + (-116248879/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628068279/5000000000 : ℝ)^4479 ≤ (10859685630883/25000000000000 : ℝ)^3455 := by
    have hnat : (2628068279 : ℕ)^4479*25000000000000^3455 ≤ 10859685630883^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628068279 5000000000 10859685630883 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425621939/10000000000 : ℝ)^4479 ≤ (9052637495083/20000000000000 : ℝ)^3455 := by
    have hnat : (5425621939 : ℕ)^4479*20000000000000^3455 ≤ 9052637495083^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425621939 10000000000 9052637495083 20000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116248879/625000000 : ℝ)^4479 ≤ (2824517494399/25000000000000 : ℝ)^3455 := by
    have hnat : (116248879 : ℕ)^4479*25000000000000^3455 ≤ 2824517494399^3455*625000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116248879 625000000 2824517494399 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628068279/5000000000 : ℝ), (5425621939/10000000000 : ℝ), (-116248879/625000000 : ℝ)] ![(10859685630883/25000000000000 : ℝ), (9052637495083/20000000000000 : ℝ), (2824517494399/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628068279/5000000000 : ℝ)|^4479 ≤ (10859685630883/25000000000000 : ℝ)^3455
        have hw : |(2628068279/5000000000 : ℝ)|=(2628068279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425621939/10000000000 : ℝ)|^4479 ≤ (9052637495083/20000000000000 : ℝ)^3455
        have hw : |(5425621939/10000000000 : ℝ)|=(5425621939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-116248879/625000000 : ℝ)|^4479 ≤ (2824517494399/25000000000000 : ℝ)^3455
        have hw : |(-116248879/625000000 : ℝ)|=(116248879/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_box_11 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (181378159/400000000 : ℝ)*x 0 + (2079391641/5000000000 : ℝ)*x 1 + (4158782983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (181378159/400000000 : ℝ)^4479 ≤ (35869487474291/100000000000000 : ℝ)^3455 := by
    have hnat : (181378159 : ℕ)^4479*100000000000000^3455 ≤ 35869487474291^3455*400000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181378159 400000000 35869487474291 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079391641/5000000000 : ℝ)^4479 ≤ (32065257755149/100000000000000 : ℝ)^3455 := by
    have hnat : (2079391641 : ℕ)^4479*100000000000000^3455 ≤ 32065257755149^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079391641 5000000000 32065257755149 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4158782983/10000000000 : ℝ)^4479 ≤ (6413050953303/20000000000000 : ℝ)^3455 := by
    have hnat : (4158782983 : ℕ)^4479*20000000000000^3455 ≤ 6413050953303^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158782983 10000000000 6413050953303 20000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(181378159/400000000 : ℝ), (2079391641/5000000000 : ℝ), (4158782983/10000000000 : ℝ)] ![(35869487474291/100000000000000 : ℝ), (32065257755149/100000000000000 : ℝ), (6413050953303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(181378159/400000000 : ℝ)|^4479 ≤ (35869487474291/100000000000000 : ℝ)^3455
        have hw : |(181378159/400000000 : ℝ)|=(181378159/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2079391641/5000000000 : ℝ)|^4479 ≤ (32065257755149/100000000000000 : ℝ)^3455
        have hw : |(2079391641/5000000000 : ℝ)|=(2079391641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4158782983/10000000000 : ℝ)|^4479 ≤ (6413050953303/20000000000000 : ℝ)^3455
        have hw : |(4158782983/10000000000 : ℝ)|=(4158782983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_box_12 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-443761039/2500000000 : ℝ)*x 0 + (220592111/400000000 : ℝ)*x 1 + (81685529/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (443761039/2500000000 : ℝ)^4479 ≤ (10633793669301/100000000000000 : ℝ)^3455 := by
    have hnat : (443761039 : ℕ)^4479*100000000000000^3455 ≤ 10633793669301^3455*2500000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443761039 2500000000 10633793669301 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220592111/400000000 : ℝ)^4479 ≤ (4623002320007/10000000000000 : ℝ)^3455 := by
    have hnat : (220592111 : ℕ)^4479*10000000000000^3455 ≤ 4623002320007^3455*400000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220592111 400000000 4623002320007 10000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81685529/156250000 : ℝ)^4479 ≤ (4313618311841/10000000000000 : ℝ)^3455 := by
    have hnat : (81685529 : ℕ)^4479*10000000000000^3455 ≤ 4313618311841^3455*156250000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81685529 156250000 4313618311841 10000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-443761039/2500000000 : ℝ), (220592111/400000000 : ℝ), (81685529/156250000 : ℝ)] ![(10633793669301/100000000000000 : ℝ), (4623002320007/10000000000000 : ℝ), (4313618311841/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-443761039/2500000000 : ℝ)|^4479 ≤ (10633793669301/100000000000000 : ℝ)^3455
        have hw : |(-443761039/2500000000 : ℝ)|=(443761039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(220592111/400000000 : ℝ)|^4479 ≤ (4623002320007/10000000000000 : ℝ)^3455
        have hw : |(220592111/400000000 : ℝ)|=(220592111/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81685529/156250000 : ℝ)|^4479 ≤ (4313618311841/10000000000000 : ℝ)^3455
        have hw : |(81685529/156250000 : ℝ)|=(81685529/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_box_13 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134851119/250000000 : ℝ)*x 0 + (-1941215271/10000000000 : ℝ)*x 1 + (5227873467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134851119/250000000 : ℝ)^4479 ≤ (44921973584413/100000000000000 : ℝ)^3455 := by
    have hnat : (134851119 : ℕ)^4479*100000000000000^3455 ≤ 44921973584413^3455*250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134851119 250000000 44921973584413 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1941215271/10000000000 : ℝ)^4479 ≤ (11941847451317/100000000000000 : ℝ)^3455 := by
    have hnat : (1941215271 : ℕ)^4479*100000000000000^3455 ≤ 11941847451317^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941215271 10000000000 11941847451317 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227873467/10000000000 : ℝ)^4479 ≤ (10784044739349/25000000000000 : ℝ)^3455 := by
    have hnat : (5227873467 : ℕ)^4479*25000000000000^3455 ≤ 10784044739349^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227873467 10000000000 10784044739349 25000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134851119/250000000 : ℝ), (-1941215271/10000000000 : ℝ), (5227873467/10000000000 : ℝ)] ![(44921973584413/100000000000000 : ℝ), (11941847451317/100000000000000 : ℝ), (10784044739349/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134851119/250000000 : ℝ)|^4479 ≤ (44921973584413/100000000000000 : ℝ)^3455
        have hw : |(134851119/250000000 : ℝ)|=(134851119/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1941215271/10000000000 : ℝ)|^4479 ≤ (11941847451317/100000000000000 : ℝ)^3455
        have hw : |(-1941215271/10000000000 : ℝ)|=(1941215271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227873467/10000000000 : ℝ)|^4479 ≤ (10784044739349/25000000000000 : ℝ)^3455
        have hw : |(5227873467/10000000000 : ℝ)|=(5227873467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_box_14 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107880891/200000000 : ℝ)*x 0 + (5227873849/10000000000 : ℝ)*x 1 + (-970607521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107880891/200000000 : ℝ)^4479 ≤ (22460985658589/50000000000000 : ℝ)^3455 := by
    have hnat : (107880891 : ℕ)^4479*50000000000000^3455 ≤ 22460985658589^3455*200000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107880891 200000000 22460985658589 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227873849/10000000000 : ℝ)^4479 ≤ (43136183043533/100000000000000 : ℝ)^3455 := by
    have hnat : (5227873849 : ℕ)^4479*100000000000000^3455 ≤ 43136183043533^3455*10000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227873849 10000000000 43136183043533 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (970607521/5000000000 : ℝ)^4479 ≤ (5970922812521/50000000000000 : ℝ)^3455 := by
    have hnat : (970607521 : ℕ)^4479*50000000000000^3455 ≤ 5970922812521^3455*5000000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970607521 5000000000 5970922812521 50000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107880891/200000000 : ℝ), (5227873849/10000000000 : ℝ), (-970607521/5000000000 : ℝ)] ![(22460985658589/50000000000000 : ℝ), (43136183043533/100000000000000 : ℝ), (5970922812521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107880891/200000000 : ℝ)|^4479 ≤ (22460985658589/50000000000000 : ℝ)^3455
        have hw : |(107880891/200000000 : ℝ)|=(107880891/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227873849/10000000000 : ℝ)|^4479 ≤ (43136183043533/100000000000000 : ℝ)^3455
        have hw : |(5227873849/10000000000 : ℝ)|=(5227873849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-970607521/5000000000 : ℝ)|^4479 ≤ (5970922812521/50000000000000 : ℝ)^3455
        have hw : |(-970607521/5000000000 : ℝ)|=(970607521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1491_box_15 (p : ℝ) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (504307373/1250000000 : ℝ)*x 0 + (551096337/1250000000 : ℝ)*x 1 + (551096207/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (504307373/1250000000 : ℝ)^4479 ≤ (30828127257849/100000000000000 : ℝ)^3455 := by
    have hnat : (504307373 : ℕ)^4479*100000000000000^3455 ≤ 30828127257849^3455*1250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504307373 1250000000 30828127257849 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551096337/1250000000 : ℝ)^4479 ≤ (4323242706601/12500000000000 : ℝ)^3455 := by
    have hnat : (551096337 : ℕ)^4479*12500000000000^3455 ≤ 4323242706601^3455*1250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551096337 1250000000 4323242706601 12500000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551096207/1250000000 : ℝ)^4479 ≤ (34585931076151/100000000000000 : ℝ)^3455 := by
    have hnat : (551096207 : ℕ)^4479*100000000000000^3455 ≤ 34585931076151^3455*1250000000^4479 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551096207 1250000000 34585931076151 100000000000000 4479 3455 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4479/1024 : ℝ)) 4479 3455 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(504307373/1250000000 : ℝ), (551096337/1250000000 : ℝ), (551096207/1250000000 : ℝ)] ![(30828127257849/100000000000000 : ℝ), (4323242706601/12500000000000 : ℝ), (34585931076151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(504307373/1250000000 : ℝ)|^4479 ≤ (30828127257849/100000000000000 : ℝ)^3455
        have hw : |(504307373/1250000000 : ℝ)|=(504307373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(551096337/1250000000 : ℝ)|^4479 ≤ (4323242706601/12500000000000 : ℝ)^3455
        have hw : |(551096337/1250000000 : ℝ)|=(551096337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(551096207/1250000000 : ℝ)|^4479 ≤ (34585931076151/100000000000000 : ℝ)^3455
        have hw : |(551096207/1250000000 : ℝ)|=(551096207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1491_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (677/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(31857/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58529/100000 : ℝ) ∧ (8009/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42933/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7739/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (677/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7739/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (677/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7739/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (677/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7739/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (677/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7739/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (677/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7739/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (677/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (677/6250 : ℝ) ^ (4477/1024 : ℝ) ≤ (1204226963877667/20000000000000000000 : ℝ) := by
    have hpowers : (677/6250 : ℝ)^4477 ≤ (1204226963877667/20000000000000000000 : ℝ)^1024 := by
      have hnat : (677 : ℕ)^4477*20000000000000000000^1024 ≤ 1204226963877667^1024*6250^4477 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        677 6250 1204226963877667 20000000000000000000 4477 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (677/6250 : ℝ)) (X := (1204226963877667/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7739/50000 : ℝ) ^ (4477/1024 : ℝ) ≤ (28666608642230727/100000000000000000000 : ℝ) := by
    have hpowers : (7739/50000 : ℝ)^4477 ≤ (28666608642230727/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7739 : ℕ)^4477*100000000000000000000^1024 ≤ 28666608642230727^1024*50000^4477 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7739 50000 28666608642230727 100000000000000000000 4477 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7739/50000 : ℝ)) (X := (28666608642230727/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001204226963877667/10000000000000000000 : ℝ) ≤ (10000275423531199/10000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (10001204226963877667/10000000000000000000 : ℝ)^1024 ≤ (10000275423531199/10000000000000000 : ℝ)^4477 := by
      have hnat : (10001204226963877667 : ℕ)^1024*10000000000000000^4477 ≤ 10000275423531199^4477*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001204226963877667 10000000000000000000 10000275423531199 10000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000275423531199/10000000000000000 : ℝ)) (X := (10001204226963877667/10000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017343871730809531/50000000000000000000 : ℝ) ≤ (5000396643944257/5000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (50017343871730809531/50000000000000000000 : ℝ)^1024 ≤ (5000396643944257/5000000000000000 : ℝ)^4477 := by
      have hnat : (50017343871730809531 : ℕ)^1024*5000000000000000^4477 ≤ 5000396643944257^4477*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017343871730809531 50000000000000000000 5000396643944257 5000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000396643944257/5000000000000000 : ℝ)) (X := (50017343871730809531/50000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028666608642230727/50000000000000000000 : ℝ) ≤ (10001311152245829/10000000000000000 : ℝ) ^ (4477/1024 : ℝ) := by
    have hpowers : (50028666608642230727/50000000000000000000 : ℝ)^1024 ≤ (10001311152245829/10000000000000000 : ℝ)^4477 := by
      have hnat : (50028666608642230727 : ℕ)^1024*10000000000000000^4477 ≤ 10001311152245829^4477*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028666608642230727 50000000000000000000 10001311152245829 10000000000000000 1024 4477 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001311152245829/10000000000000000 : ℝ)) (X := (50028666608642230727/50000000000000000000 : ℝ)) (by norm_num) 4477 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1204226963877667/20000000000000000000 : ℝ) ≤ ((23225030302144539197/23230000000000000000 : ℝ)+2*(103572871463/92920000000000 : ℝ)*(677/6250 : ℝ))^(4477/1024 : ℝ) := by
    rw [show (23225030302144539197/23230000000000000000 : ℝ)+2*(103572871463/92920000000000 : ℝ)*(677/6250 : ℝ)=(10000275423531199/10000000000000000 : ℝ) by norm_num, show 1+2*(1204226963877667/20000000000000000000 : ℝ)=(10001204226963877667/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28666608642230727/100000000000000000000 : ℝ)+(1204226963877667/20000000000000000000 : ℝ) ≤ ((23225030302144539197/23230000000000000000 : ℝ)+(103572871463/92920000000000 : ℝ)*((7739/50000 : ℝ)+(677/6250 : ℝ)))^(4477/1024 : ℝ) := by
    rw [show (23225030302144539197/23230000000000000000 : ℝ)+(103572871463/92920000000000 : ℝ)*((7739/50000 : ℝ)+(677/6250 : ℝ))=(5000396643944257/5000000000000000 : ℝ) by norm_num, show 1+(28666608642230727/100000000000000000000 : ℝ)+(1204226963877667/20000000000000000000 : ℝ)=(50017343871730809531/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28666608642230727/100000000000000000000 : ℝ) ≤ ((23225030302144539197/23230000000000000000 : ℝ)+2*(103572871463/92920000000000 : ℝ)*(7739/50000 : ℝ))^(4477/1024 : ℝ) := by
    rw [show (23225030302144539197/23230000000000000000 : ℝ)+2*(103572871463/92920000000000 : ℝ)*(7739/50000 : ℝ)=(10001311152245829/10000000000000000 : ℝ) by norm_num, show 1+2*(28666608642230727/100000000000000000000 : ℝ)=(50028666608642230727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23225030302144539197/23230000000000000000 : ℝ)*(X 1 0+X 2 0)+(103572871463/92920000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (677/6250 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (23225030302144539197/23230000000000000000 : ℝ)) (alpha := (103572871463/92920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23225030302144539197/23230000000000000000 : ℝ)*(X 0 1+X 2 1)+(103572871463/92920000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (677/6250 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (23225030302144539197/23230000000000000000 : ℝ)) (alpha := (103572871463/92920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23225030302144539197/23230000000000000000 : ℝ)*(X 0 2+X 1 2)+(103572871463/92920000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4477/1024 : ℝ)) (lo := (677/6250 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (23225030302144539197/23230000000000000000 : ℝ)) (alpha := (103572871463/92920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-420507907/2500000000 : ℝ)*X 0 0+(5405107077/10000000000 : ℝ)*X 0 1+(1351276793/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635225163/5000000000 : ℝ)*X 1 0+(-373730699/2000000000 : ℝ)*X 1 1+(2702553399/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270449601/10000000000 : ℝ)*X 2 0+(5405107289/10000000000 : ℝ)*X 2 1+(-116790863/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4483707563/10000000000 : ℝ)*X 0 0+(4184748347/10000000000 : ℝ)*X 0 1+(2092373657/5000000000 : ℝ)*X 0 2+(4483707563/10000000000 : ℝ)*X 1 0+(4184748347/10000000000 : ℝ)*X 1 1+(2092373657/5000000000 : ℝ)*X 1 2+(4483707563/10000000000 : ℝ)*X 2 0+(4184748347/10000000000 : ℝ)*X 2 1+(2092373657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-84896501/400000000 : ℝ)*X 0 0+(1310719987/2500000000 : ℝ)*X 0 1+(5242880183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5383580781/10000000000 : ℝ)*X 1 0+(-1935237673/10000000000 : ℝ)*X 1 1+(1310720033/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1076716081/2000000000 : ℝ)*X 2 0+(5242880321/10000000000 : ℝ)*X 2 1+(-241904741/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4073283559/10000000000 : ℝ)*X 0 0+(877964561/2000000000 : ℝ)*X 0 1+(548727829/1250000000 : ℝ)*X 0 2+(4073283559/10000000000 : ℝ)*X 1 0+(877964561/2000000000 : ℝ)*X 1 1+(548727829/1250000000 : ℝ)*X 1 2+(4073283559/10000000000 : ℝ)*X 2 0+(877964561/2000000000 : ℝ)*X 2 1+(548727829/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2029466809/10000000000 : ℝ)*X 0 0+(128236593/250000000 : ℝ)*X 0 1+(54256217/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1051227379/2000000000 : ℝ)*X 1 0+(-929991059/5000000000 : ℝ)*X 1 1+(2712810783/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2628068279/5000000000 : ℝ)*X 2 0+(5425621939/10000000000 : ℝ)*X 2 1+(-116248879/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((181378159/400000000 : ℝ)*X 0 0+(2079391641/5000000000 : ℝ)*X 0 1+(4158782983/10000000000 : ℝ)*X 0 2+(181378159/400000000 : ℝ)*X 1 0+(2079391641/5000000000 : ℝ)*X 1 1+(4158782983/10000000000 : ℝ)*X 1 2+(181378159/400000000 : ℝ)*X 2 0+(2079391641/5000000000 : ℝ)*X 2 1+(4158782983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-443761039/2500000000 : ℝ)*X 0 0+(220592111/400000000 : ℝ)*X 0 1+(81685529/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((134851119/250000000 : ℝ)*X 1 0+(-1941215271/10000000000 : ℝ)*X 1 1+(5227873467/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((107880891/200000000 : ℝ)*X 2 0+(5227873849/10000000000 : ℝ)*X 2 1+(-970607521/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((504307373/1250000000 : ℝ)*X 0 0+(551096337/1250000000 : ℝ)*X 0 1+(551096207/1250000000 : ℝ)*X 0 2+(504307373/1250000000 : ℝ)*X 1 0+(551096337/1250000000 : ℝ)*X 1 1+(551096207/1250000000 : ℝ)*X 1 2+(504307373/1250000000 : ℝ)*X 2 0+(551096337/1250000000 : ℝ)*X 2 1+(551096207/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1491_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31857/50000 : ℝ) ≤ (-2960027526912652842891398367/4646000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59162751/50000000000000 : ℝ)*(upper1) + (36978133/25000000000000 : ℝ)*(lower4) + (36086353/100000000000000 : ℝ)*(upper5) + (2192193606117599/100000000000000 : ℝ)*(major0) + (2192193606117599/100000000000000 : ℝ)*(major1) + (2192193606117599/100000000000000 : ℝ)*(major2) + (1349276977/100000000000000 : ℝ)*(sp3) + (1524968375746801/50000000000000 : ℝ)*(sp4) + (1524934134030307/50000000000000 : ℝ)*(sp5) + (3049900029881711/100000000000000 : ℝ)*(sp6) + (21182584822653/1562500000000 : ℝ)*(sp7) + (786609573/100000000000000 : ℝ)*(sp12) + (69270042561/100000000000000 : ℝ)*(sp13) + (4688527683/12500000000000 : ℝ)*(sp14) + (1355686777926769/100000000000000 : ℝ)*(f.failure) + (1524968769051587/50000000000000 : ℝ)*(f.sum) + (19630077497051/4646000000000000000000000000 : ℝ)*base65 + (6559213781668721997/2323000000000000000000000000000000 : ℝ)*base68 + (1165867835133278003/2323000000000000000000000000000000 : ℝ)*base69 + (14180843073002278003/2323000000000000000000000000000000 : ℝ)*base71 + (20339353575259/4646000000000000000000000000 : ℝ)*base74 + (5296340400929721997/2323000000000000000000000000000000 : ℝ)*base76 + (7032497574699278003/2323000000000000000000000000000000 : ℝ)*base77 + (1234308659576721997/2323000000000000000000000000000000 : ℝ)*base80 + (6722544099459/4646000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (46450357/10000000000000000000000 : ℝ)*base90 + (46450357/10000000000000000000000 : ℝ)*base92 + (46450357/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58529/100000 : ℝ) ≤ (679844419775437501247149749281889/1161500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (193582697/100000000000000 : ℝ)*(lower0) + (36074141/20000000000000 : ℝ)*(upper2) + (64492233/100000000000000 : ℝ)*(upper3) + (11603479/100000000000000 : ℝ)*(lower5) + (2267007661214279/100000000000000 : ℝ)*(major0) + (2267007661214279/100000000000000 : ℝ)*(major1) + (2267007661214279/100000000000000 : ℝ)*(major2) + (1556275916921701/50000000000000 : ℝ)*(sp0) + (3112463652650433/100000000000000 : ℝ)*(sp1) + (3112495292240669/100000000000000 : ℝ)*(sp2) + (700976412137611/50000000000000 : ℝ)*(sp3) + (134254673/100000000000000 : ℝ)*(sp7) + (88181192969/100000000000000 : ℝ)*(sp9) + (56541602733/100000000000000 : ℝ)*(sp10) + (280390591705979/20000000000000 : ℝ)*(f.failure) + (1556275916921701/50000000000000 : ℝ)*(f.sum) + (376261692803/185840000000000000000000000 : ℝ)*base65 + (11257403839243156037/2323000000000000000000000000000000 : ℝ)*base68 + (5222157929748156037/2323000000000000000000000000000000 : ℝ)*base70 + (10613232654237843963/2323000000000000000000000000000000 : ℝ)*base71 + (5688122497873/929200000000000000000000000 : ℝ)*base73 + (4908166949360156037/2323000000000000000000000000000000 : ℝ)*base76 + (9877646178827843963/2323000000000000000000000000000000 : ℝ)*base77 + (9587955901945156037/2323000000000000000000000000000000 : ℝ)*base80 + (22716402718503/4646000000000000000000000000 : ℝ)*base82 + (5407513/2000000000000000000000 : ℝ)*base89 + (5407513/2000000000000000000000 : ℝ)*base91 + (5407513/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (8009/10000 : ℝ) ≤ (46513955021414832878259034558533/58075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43115847/100000000000000 : ℝ)*(upper1) + (6022017/20000000000000 : ℝ)*(upper2) + (34899769/100000000000000 : ℝ)*(lower5) + (123165697721637/5000000000000 : ℝ)*(major0) + (123165697721637/5000000000000 : ℝ)*(major1) + (123165697721637/5000000000000 : ℝ)*(major2) + (3563375937/20000000000000 : ℝ)*(sp1) + (76281945181/100000000000000 : ℝ)*(sp2) + (2918137589/25000000000000 : ℝ)*(sp3) + (2116717709/100000000000000 : ℝ)*(sp4) + (337657631945209/10000000000000 : ℝ)*(sp8) + (1688280309645057/50000000000000 : ℝ)*(sp9) + (1688251077112309/50000000000000 : ℝ)*(sp10) + (1523340164891243/100000000000000 : ℝ)*(sp11) + (1523351837441599/100000000000000 : ℝ)*(f.failure) + (3376578436169799/100000000000000 : ℝ)*(f.sum) + (1231377080101/580750000000000000000000000 : ℝ)*base66 + (664340386285755489/116150000000000000000000000000000 : ℝ)*base67 + (36359102664255489/116150000000000000000000000000000 : ℝ)*base69 + (55304178982305489/116150000000000000000000000000000 : ℝ)*base71 + (10754896825797/2323000000000000000000000000 : ℝ)*base73 + (1303429220058794511/116150000000000000000000000000000 : ℝ)*base76 + (3180166720444511/116150000000000000000000000000000 : ℝ)*base78 + (914011236819905489/116150000000000000000000000000000 : ℝ)*base79 + (9656793862209/2323000000000000000000000000 : ℝ)*base82 + (36348347/10000000000000000000000 : ℝ)*base90 + (36348347/10000000000000000000000 : ℝ)*base92 + (36348347/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42933/50000 : ℝ) ≤ (-498651068318297005689915779450163/580750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (99608763/100000000000000 : ℝ)*(lower0) + (26215451/50000000000000 : ℝ)*(upper1) + (5875999/20000000000000 : ℝ)*(lower2) + (7994247/12500000000000 : ℝ)*(upper3) + (15260551/20000000000000 : ℝ)*(upper5) + (1250939311956293/50000000000000 : ℝ)*(major0) + (1250939311956293/50000000000000 : ℝ)*(major1) + (1250939311956293/50000000000000 : ℝ)*(major2) + (1225259567/1250000000000 : ℝ)*(sp5) + (1777248361/50000000000000 : ℝ)*(sp7) + (871294378389739/25000000000000 : ℝ)*(sp12) + (871269873198399/25000000000000 : ℝ)*(sp13) + (871294378389739/25000000000000 : ℝ)*(sp14) + (773598638552223/50000000000000 : ℝ)*(sp15) + (96700051975073/6250000000000 : ℝ)*(f.failure) + (871294378389739/25000000000000 : ℝ)*(f.sum) + (1477707115639/2323000000000000000000000000 : ℝ)*base66 + (1375381248805066721/1161500000000000000000000000000000 : ℝ)*base67 + (4772310316370066721/1161500000000000000000000000000000 : ℝ)*base69 + (3451089201738933279/1161500000000000000000000000000000 : ℝ)*base72 + (4297102457569/2323000000000000000000000000 : ℝ)*base73 + (9387309282036066721/1161500000000000000000000000000000 : ℝ)*base75 + (6289315130558933279/1161500000000000000000000000000000 : ℝ)*base78 + (3329908447649066721/1161500000000000000000000000000000 : ℝ)*base79 + (2478998019503/464600000000000000000000000 : ℝ)*base81 + (2816069/625000000000000000000 : ℝ)*base90 + (2816069/625000000000000000000 : ℝ)*base92 + (2816069/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1491_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (677/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31857/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58529/100000 : ℝ) else (8009/10000 : ℝ) ≤ X j i ∧ X j i ≤ (42933/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1491_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1491_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10831/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31857/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58529/100000 : ℝ) else (8009/10000 : ℝ) ≤ X j i ∧ X j i ≤ (42933/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1491_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1491_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4477/1024 : ℝ) ≤ p) (hpb : p ≤ (4479/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161703547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10831/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31857/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58529/100000 : ℝ) else (8009/10000 : ℝ) ≤ X j i ∧ X j i ≤ (42933/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1491_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

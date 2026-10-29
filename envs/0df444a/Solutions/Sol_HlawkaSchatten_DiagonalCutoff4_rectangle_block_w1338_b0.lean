-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1338_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:03:27.986264+00:00
-- url     : https://prove2.me/submissions/ed84de6d-e885-4d0a-a474-d5f9afc39c6d

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
theorem support_rectangle_w1338_s0_0 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1811513271/10000000000 : ℝ)*x 0 + (5998646143/10000000000 : ℝ)*x 1 + (480995377/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1811513271/10000000000 : ℝ)^2149 ≤ (10616496019487/100000000000000 : ℝ)^1637 := by
    have hnat : (1811513271 : ℕ)^2149*100000000000000^1637 ≤ 10616496019487^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811513271 10000000000 10616496019487 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5998646143/10000000000 : ℝ)^2149 ≤ (25562632124461/50000000000000 : ℝ)^1637 := by
    have hnat : (5998646143 : ℕ)^2149*50000000000000^1637 ≤ 25562632124461^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5998646143 10000000000 25562632124461 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (480995377/1000000000 : ℝ)^2149 ≤ (19129119861149/50000000000000 : ℝ)^1637 := by
    have hnat : (480995377 : ℕ)^2149*50000000000000^1637 ≤ 19129119861149^1637*1000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480995377 1000000000 19129119861149 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1811513271/10000000000 : ℝ), (5998646143/10000000000 : ℝ), (480995377/1000000000 : ℝ)] ![(10616496019487/100000000000000 : ℝ), (25562632124461/50000000000000 : ℝ), (19129119861149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1811513271/10000000000 : ℝ)|^2149 ≤ (10616496019487/100000000000000 : ℝ)^1637
        have hw : |(-1811513271/10000000000 : ℝ)|=(1811513271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5998646143/10000000000 : ℝ)|^2149 ≤ (25562632124461/50000000000000 : ℝ)^1637
        have hw : |(5998646143/10000000000 : ℝ)|=(5998646143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(480995377/1000000000 : ℝ)|^2149 ≤ (19129119861149/50000000000000 : ℝ)^1637
        have hw : |(480995377/1000000000 : ℝ)|=(480995377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s0_1 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2751130319/5000000000 : ℝ)*x 0 + (-2487357209/10000000000 : ℝ)*x 1 + (4809954157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2751130319/5000000000 : ℝ)^2149 ≤ (11411190018871/25000000000000 : ℝ)^1637 := by
    have hnat : (2751130319 : ℕ)^2149*25000000000000^1637 ≤ 11411190018871^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751130319 5000000000 11411190018871 25000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2487357209/10000000000 : ℝ)^2149 ≤ (8048498071621/50000000000000 : ℝ)^1637 := by
    have hnat : (2487357209 : ℕ)^2149*50000000000000^1637 ≤ 8048498071621^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2487357209 10000000000 8048498071621 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4809954157/10000000000 : ℝ)^2149 ≤ (19129121881621/50000000000000 : ℝ)^1637 := by
    have hnat : (4809954157 : ℕ)^2149*50000000000000^1637 ≤ 19129121881621^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4809954157 10000000000 19129121881621 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2751130319/5000000000 : ℝ), (-2487357209/10000000000 : ℝ), (4809954157/10000000000 : ℝ)] ![(11411190018871/25000000000000 : ℝ), (8048498071621/50000000000000 : ℝ), (19129121881621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2751130319/5000000000 : ℝ)|^2149 ≤ (11411190018871/25000000000000 : ℝ)^1637
        have hw : |(2751130319/5000000000 : ℝ)|=(2751130319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2487357209/10000000000 : ℝ)|^2149 ≤ (8048498071621/50000000000000 : ℝ)^1637
        have hw : |(-2487357209/10000000000 : ℝ)|=(2487357209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4809954157/10000000000 : ℝ)|^2149 ≤ (19129121881621/50000000000000 : ℝ)^1637
        have hw : |(4809954157/10000000000 : ℝ)|=(4809954157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s0_2 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5502260269/10000000000 : ℝ)*x 0 + (18788883/39062500 : ℝ)*x 1 + (-2487357817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5502260269/10000000000 : ℝ)^2149 ≤ (9128951211397/20000000000000 : ℝ)^1637 := by
    have hnat : (5502260269 : ℕ)^2149*20000000000000^1637 ≤ 9128951211397^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502260269 10000000000 9128951211397 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18788883/39062500 : ℝ)^2149 ≤ (7651648525019/20000000000000 : ℝ)^1637 := by
    have hnat : (18788883 : ℕ)^2149*20000000000000^1637 ≤ 7651648525019^1637*39062500^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18788883 39062500 7651648525019 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2487357817/10000000000 : ℝ)^2149 ≤ (16097001308571/100000000000000 : ℝ)^1637 := by
    have hnat : (2487357817 : ℕ)^2149*100000000000000^1637 ≤ 16097001308571^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2487357817 10000000000 16097001308571 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5502260269/10000000000 : ℝ), (18788883/39062500 : ℝ), (-2487357817/10000000000 : ℝ)] ![(9128951211397/20000000000000 : ℝ), (7651648525019/20000000000000 : ℝ), (16097001308571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5502260269/10000000000 : ℝ)|^2149 ≤ (9128951211397/20000000000000 : ℝ)^1637
        have hw : |(5502260269/10000000000 : ℝ)|=(5502260269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(18788883/39062500 : ℝ)|^2149 ≤ (7651648525019/20000000000000 : ℝ)^1637
        have hw : |(18788883/39062500 : ℝ)|=(18788883/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2487357817/10000000000 : ℝ)|^2149 ≤ (16097001308571/100000000000000 : ℝ)^1637
        have hw : |(-2487357817/10000000000 : ℝ)|=(2487357817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s0_3 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4179346087/10000000000 : ℝ)*x 0 + (48543223/156250000 : ℝ)*x 1 + (69910261/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4179346087/10000000000 : ℝ)^2149 ≤ (3976614049817/12500000000000 : ℝ)^1637 := by
    have hnat : (4179346087 : ℕ)^2149*12500000000000^1637 ≤ 3976614049817^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4179346087 10000000000 3976614049817 12500000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48543223/156250000 : ℝ)^2149 ≤ (21553575705679/100000000000000 : ℝ)^1637 := by
    have hnat : (48543223 : ℕ)^2149*100000000000000^1637 ≤ 21553575705679^1637*156250000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48543223 156250000 21553575705679 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69910261/125000000 : ℝ)^2149 ≤ (23316755940751/50000000000000 : ℝ)^1637 := by
    have hnat : (69910261 : ℕ)^2149*50000000000000^1637 ≤ 23316755940751^1637*125000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69910261 125000000 23316755940751 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4179346087/10000000000 : ℝ), (48543223/156250000 : ℝ), (69910261/125000000 : ℝ)] ![(3976614049817/12500000000000 : ℝ), (21553575705679/100000000000000 : ℝ), (23316755940751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4179346087/10000000000 : ℝ)|^2149 ≤ (3976614049817/12500000000000 : ℝ)^1637
        have hw : |(4179346087/10000000000 : ℝ)|=(4179346087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(48543223/156250000 : ℝ)|^2149 ≤ (21553575705679/100000000000000 : ℝ)^1637
        have hw : |(48543223/156250000 : ℝ)|=(48543223/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(69910261/125000000 : ℝ)|^2149 ≤ (23316755940751/50000000000000 : ℝ)^1637
        have hw : |(69910261/125000000 : ℝ)|=(69910261/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s0_4 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-453997717/2500000000 : ℝ)*x 0 + (605069399/1250000000 : ℝ)*x 1 + (5966952389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (453997717/2500000000 : ℝ)^2149 ≤ (10650957994661/100000000000000 : ℝ)^1637 := by
    have hnat : (453997717 : ℕ)^2149*100000000000000^1637 ≤ 10650957994661^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453997717 2500000000 10650957994661 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605069399/1250000000 : ℝ)^2149 ≤ (1205565265171/3125000000000 : ℝ)^1637 := by
    have hnat : (605069399 : ℕ)^2149*3125000000000^1637 ≤ 1205565265171^1637*1250000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605069399 1250000000 1205565265171 3125000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5966952389/10000000000 : ℝ)^2149 ≤ (25385476752987/50000000000000 : ℝ)^1637 := by
    have hnat : (5966952389 : ℕ)^2149*50000000000000^1637 ≤ 25385476752987^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5966952389 10000000000 25385476752987 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-453997717/2500000000 : ℝ), (605069399/1250000000 : ℝ), (5966952389/10000000000 : ℝ)] ![(10650957994661/100000000000000 : ℝ), (1205565265171/3125000000000 : ℝ), (25385476752987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-453997717/2500000000 : ℝ)|^2149 ≤ (10650957994661/100000000000000 : ℝ)^1637
        have hw : |(-453997717/2500000000 : ℝ)|=(453997717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(605069399/1250000000 : ℝ)|^2149 ≤ (1205565265171/3125000000000 : ℝ)^1637
        have hw : |(605069399/1250000000 : ℝ)|=(605069399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5966952389/10000000000 : ℝ)|^2149 ≤ (25385476752987/50000000000000 : ℝ)^1637
        have hw : |(5966952389/10000000000 : ℝ)|=(5966952389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s0_5 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2589164413/5000000000 : ℝ)*x 0 + (-13303599/100000000 : ℝ)*x 1 + (2983476099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589164413/5000000000 : ℝ)^2149 ≤ (5268749014697/12500000000000 : ℝ)^1637 := by
    have hnat : (2589164413 : ℕ)^2149*12500000000000^1637 ≤ 5268749014697^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589164413 5000000000 5268749014697 12500000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13303599/100000000 : ℝ)^2149 ≤ (7079056496221/100000000000000 : ℝ)^1637 := by
    have hnat : (13303599 : ℕ)^2149*100000000000000^1637 ≤ 7079056496221^1637*100000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13303599 100000000 7079056496221 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2983476099/5000000000 : ℝ)^2149 ≤ (50770951372517/100000000000000 : ℝ)^1637 := by
    have hnat : (2983476099 : ℕ)^2149*100000000000000^1637 ≤ 50770951372517^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2983476099 5000000000 50770951372517 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589164413/5000000000 : ℝ), (-13303599/100000000 : ℝ), (2983476099/5000000000 : ℝ)] ![(5268749014697/12500000000000 : ℝ), (7079056496221/100000000000000 : ℝ), (50770951372517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589164413/5000000000 : ℝ)|^2149 ≤ (5268749014697/12500000000000 : ℝ)^1637
        have hw : |(2589164413/5000000000 : ℝ)|=(2589164413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13303599/100000000 : ℝ)|^2149 ≤ (7079056496221/100000000000000 : ℝ)^1637
        have hw : |(-13303599/100000000 : ℝ)|=(13303599/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2983476099/5000000000 : ℝ)|^2149 ≤ (50770951372517/100000000000000 : ℝ)^1637
        have hw : |(2983476099/5000000000 : ℝ)|=(2983476099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s0_6 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5178328827/10000000000 : ℝ)*x 0 + (5966952379/10000000000 : ℝ)*x 1 + (-166294951/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5178328827/10000000000 : ℝ)^2149 ≤ (42149992128261/100000000000000 : ℝ)^1637 := by
    have hnat : (5178328827 : ℕ)^2149*100000000000000^1637 ≤ 42149992128261^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178328827 10000000000 42149992128261 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5966952379/10000000000 : ℝ)^2149 ≤ (25385476697137/50000000000000 : ℝ)^1637 := by
    have hnat : (5966952379 : ℕ)^2149*50000000000000^1637 ≤ 25385476697137^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5966952379 10000000000 25385476697137 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166294951/1250000000 : ℝ)^2149 ≤ (7079054456471/100000000000000 : ℝ)^1637 := by
    have hnat : (166294951 : ℕ)^2149*100000000000000^1637 ≤ 7079054456471^1637*1250000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166294951 1250000000 7079054456471 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5178328827/10000000000 : ℝ), (5966952379/10000000000 : ℝ), (-166294951/1250000000 : ℝ)] ![(42149992128261/100000000000000 : ℝ), (25385476697137/50000000000000 : ℝ), (7079054456471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5178328827/10000000000 : ℝ)|^2149 ≤ (42149992128261/100000000000000 : ℝ)^1637
        have hw : |(5178328827/10000000000 : ℝ)|=(5178328827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5966952379/10000000000 : ℝ)|^2149 ≤ (25385476697137/50000000000000 : ℝ)^1637
        have hw : |(5966952379/10000000000 : ℝ)|=(5966952379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-166294951/1250000000 : ℝ)|^2149 ≤ (7079054456471/100000000000000 : ℝ)^1637
        have hw : |(-166294951/1250000000 : ℝ)|=(166294951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s0_7 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1047177259/2500000000 : ℝ)*x 0 + (552882129/1000000000 : ℝ)*x 1 + (3173050587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047177259/2500000000 : ℝ)^2149 ≤ (31906506296617/100000000000000 : ℝ)^1637 := by
    have hnat : (1047177259 : ℕ)^2149*100000000000000^1637 ≤ 31906506296617^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047177259 2500000000 31906506296617 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552882129/1000000000 : ℝ)^2149 ≤ (22967115051007/50000000000000 : ℝ)^1637 := by
    have hnat : (552882129 : ℕ)^2149*50000000000000^1637 ≤ 22967115051007^1637*1000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552882129 1000000000 22967115051007 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3173050587/10000000000 : ℝ)^2149 ≤ (4431852716127/20000000000000 : ℝ)^1637 := by
    have hnat : (3173050587 : ℕ)^2149*20000000000000^1637 ≤ 4431852716127^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3173050587 10000000000 4431852716127 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047177259/2500000000 : ℝ), (552882129/1000000000 : ℝ), (3173050587/10000000000 : ℝ)] ![(31906506296617/100000000000000 : ℝ), (22967115051007/50000000000000 : ℝ), (4431852716127/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047177259/2500000000 : ℝ)|^2149 ≤ (31906506296617/100000000000000 : ℝ)^1637
        have hw : |(1047177259/2500000000 : ℝ)|=(1047177259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552882129/1000000000 : ℝ)|^2149 ≤ (22967115051007/50000000000000 : ℝ)^1637
        have hw : |(552882129/1000000000 : ℝ)|=(552882129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3173050587/10000000000 : ℝ)|^2149 ≤ (4431852716127/20000000000000 : ℝ)^1637
        have hw : |(3173050587/10000000000 : ℝ)|=(3173050587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1338_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (173/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (269/1000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4297/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4297 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4297*1^1024 ≤ 0^1024*1^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4297/1024 : ℝ) ≤ (2138595723689731027/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4297 ≤ (2138595723689731027/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4297*100000000000000000000^1024 ≤ 2138595723689731027^1024*5^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2138595723689731027 100000000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2138595723689731027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4297 := by
      have hnat : (1 : ℕ)^1024*1^4297 ≤ 1^4297*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102138595723689731027/100000000000000000000 : ℝ) ≤ (10050554022158447/10000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (102138595723689731027/100000000000000000000 : ℝ)^1024 ≤ (10050554022158447/10000000000000000 : ℝ)^4297 := by
      have hnat : (102138595723689731027 : ℕ)^1024*10000000000000000^4297 ≤ 10050554022158447^4297*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102138595723689731027 100000000000000000000 10050554022158447 10000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10050554022158447/10000000000000000 : ℝ)) (X := (102138595723689731027/100000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52138595723689731027/50000000000000000000 : ℝ) ≤ (5050554022158447/5000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (52138595723689731027/50000000000000000000 : ℝ)^1024 ≤ (5050554022158447/5000000000000000 : ℝ)^4297 := by
      have hnat : (52138595723689731027 : ℕ)^1024*5000000000000000^4297 ≤ 5050554022158447^4297*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52138595723689731027 50000000000000000000 5050554022158447 5000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5050554022158447/5000000000000000 : ℝ)) (X := (52138595723689731027/50000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(50554022158447/4000000000000000 : ℝ)*(0 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(50554022158447/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2138595723689731027/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(50554022158447/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4297/1024 : ℝ) := by
    rw [show (1 : ℝ)+(50554022158447/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10050554022158447/10000000000000000 : ℝ) by norm_num, show 1+(2138595723689731027/100000000000000000000 : ℝ)+(0 : ℝ)=(102138595723689731027/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2138595723689731027/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(50554022158447/4000000000000000 : ℝ)*(2/5 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(50554022158447/4000000000000000 : ℝ)*(2/5 : ℝ)=(5050554022158447/5000000000000000 : ℝ) by norm_num, show 1+2*(2138595723689731027/100000000000000000000 : ℝ)=(52138595723689731027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(50554022158447/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50554022158447/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(50554022158447/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50554022158447/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(50554022158447/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50554022158447/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1811513271/10000000000 : ℝ)*X 0 0+(5998646143/10000000000 : ℝ)*X 0 1+(480995377/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2751130319/5000000000 : ℝ)*X 1 0+(-2487357209/10000000000 : ℝ)*X 1 1+(4809954157/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5502260269/10000000000 : ℝ)*X 2 0+(18788883/39062500 : ℝ)*X 2 1+(-2487357817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4179346087/10000000000 : ℝ)*X 0 0+(48543223/156250000 : ℝ)*X 0 1+(69910261/125000000 : ℝ)*X 0 2+(4179346087/10000000000 : ℝ)*X 1 0+(48543223/156250000 : ℝ)*X 1 1+(69910261/125000000 : ℝ)*X 1 2+(4179346087/10000000000 : ℝ)*X 2 0+(48543223/156250000 : ℝ)*X 2 1+(69910261/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-453997717/2500000000 : ℝ)*X 0 0+(605069399/1250000000 : ℝ)*X 0 1+(5966952389/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2589164413/5000000000 : ℝ)*X 1 0+(-13303599/100000000 : ℝ)*X 1 1+(2983476099/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5178328827/10000000000 : ℝ)*X 2 0+(5966952379/10000000000 : ℝ)*X 2 1+(-166294951/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1047177259/2500000000 : ℝ)*X 0 0+(552882129/1000000000 : ℝ)*X 0 1+(3173050587/10000000000 : ℝ)*X 0 2+(1047177259/2500000000 : ℝ)*X 1 0+(552882129/1000000000 : ℝ)*X 1 1+(3173050587/10000000000 : ℝ)*X 1 2+(1047177259/2500000000 : ℝ)*X 2 0+(552882129/1000000000 : ℝ)*X 2 1+(3173050587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1173070476750320492946819/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101920977/100000000000000 : ℝ)*(base1) + (1412804733/100000000000000 : ℝ)*(base19) + (678193233/50000000000000 : ℝ)*(base23) + (9408811/4000000000000 : ℝ)*(upper3) + (31248873/50000000000000 : ℝ)*(upper5) + (621758973981253/100000000000000 : ℝ)*(major0) + (621758973981253/100000000000000 : ℝ)*(major1) + (621758973981253/100000000000000 : ℝ)*(major2) + (210316406017543/25000000000000 : ℝ)*(sp0) + (420634135770119/50000000000000 : ℝ)*(sp1) + (168253665591701/20000000000000 : ℝ)*(sp2) + (80449118816949/20000000000000 : ℝ)*(sp3) + (65034309/1562500000000 : ℝ)*(sp4) + (74128127/3125000000000 : ℝ)*(sp7) + (201124034052893/50000000000000 : ℝ)*(f.failure) + (841269684344971/100000000000000 : ℝ)*(f.sum) + (79639014205909/200000000000000000000000000000 : ℝ)*base66 + (257620458394091/400000000000000000000000000000 : ℝ)*base67 + (1851408215205909/400000000000000000000000000000 : ℝ)*base70 + (2030369211605909/400000000000000000000000000000 : ℝ)*base72 + (774618481994091/200000000000000000000000000000 : ℝ)*base73 + (617813040005909/400000000000000000000000000000 : ℝ)*base76 + (735003612005909/400000000000000000000000000000 : ℝ)*base78 + (1276124602405909/400000000000000000000000000000 : ℝ)*base80 + (416105943005909/200000000000000000000000000000 : ℝ)*base82 + (6846001/1250000000000000000000 : ℝ)*base89 + (6846001/1250000000000000000000 : ℝ)*base91 + (6846001/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1246945813151705719541241/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (687255289/50000000000000 : ℝ)*(base19) + (11256317/800000000000 : ℝ)*(base23) + (15680661/100000000000000 : ℝ)*(base39) + (3629417/2000000000000 : ℝ)*(upper3) + (40252507/25000000000000 : ℝ)*(upper5) + (65613794197019/10000000000000 : ℝ)*(major0) + (65613794197019/10000000000000 : ℝ)*(major1) + (656137926289529/100000000000000 : ℝ)*(major2) + (3076229261/100000000000000 : ℝ)*(sp1) + (3348946341/100000000000000 : ℝ)*(sp2) + (221946514543239/25000000000000 : ℝ)*(sp4) + (887781607433117/100000000000000 : ℝ)*(sp5) + (887781317867651/100000000000000 : ℝ)*(sp6) + (53061200282807/12500000000000 : ℝ)*(sp7) + (53061200282807/12500000000000 : ℝ)*(f.failure) + (887786073853617/100000000000000 : ℝ)*(f.sum) + (858463322496393/400000000000000000000000000000 : ℝ)*base65 + (273332118201463/400000000000000000000000000000 : ℝ)*base67 + (146979410829493/40000000000000000000000000000 : ℝ)*base69 + (639762195398537/400000000000000000000000000000 : ℝ)*base72 + (1419903009296393/400000000000000000000000000000 : ℝ)*base73 + (160029920469493/40000000000000000000000000000 : ℝ)*base75 + (37572587810507/40000000000000000000000000000 : ℝ)*base78 + (132916819589493/40000000000000000000000000000 : ℝ)*base79 + (60535087729493/20000000000000000000000000000 : ℝ)*base81 + (1571101/312500000000000000000 : ℝ)*base90 + (1571101/312500000000000000000 : ℝ)*base92 + (1571101/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1338_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (173/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (269/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1338_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1338_s1_0 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-31201647/156250000 : ℝ)*x 0 + (5643935843/10000000000 : ℝ)*x 1 + (5045941137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31201647/156250000 : ℝ)^2149 ≤ (75407100617/625000000000 : ℝ)^1637 := by
    have hnat : (31201647 : ℕ)^2149*625000000000^1637 ≤ 75407100617^1637*156250000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31201647 156250000 75407100617 625000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5643935843/10000000000 : ℝ)^2149 ≤ (47193813631309/100000000000000 : ℝ)^1637 := by
    have hnat : (5643935843 : ℕ)^2149*100000000000000^1637 ≤ 47193813631309^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5643935843 10000000000 47193813631309 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5045941137/10000000000 : ℝ)^2149 ≤ (20370525127569/50000000000000 : ℝ)^1637 := by
    have hnat : (5045941137 : ℕ)^2149*50000000000000^1637 ≤ 20370525127569^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5045941137 10000000000 20370525127569 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31201647/156250000 : ℝ), (5643935843/10000000000 : ℝ), (5045941137/10000000000 : ℝ)] ![(75407100617/625000000000 : ℝ), (47193813631309/100000000000000 : ℝ), (20370525127569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31201647/156250000 : ℝ)|^2149 ≤ (75407100617/625000000000 : ℝ)^1637
        have hw : |(-31201647/156250000 : ℝ)|=(31201647/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5643935843/10000000000 : ℝ)|^2149 ≤ (47193813631309/100000000000000 : ℝ)^1637
        have hw : |(5643935843/10000000000 : ℝ)|=(5643935843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5045941137/10000000000 : ℝ)|^2149 ≤ (20370525127569/50000000000000 : ℝ)^1637
        have hw : |(5045941137/10000000000 : ℝ)|=(5045941137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s1_1 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (675766977/1250000000 : ℝ)*x 0 + (-2316119243/10000000000 : ℝ)*x 1 + (5045941001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675766977/1250000000 : ℝ)^2149 ≤ (22300404521889/50000000000000 : ℝ)^1637 := by
    have hnat : (675766977 : ℕ)^2149*50000000000000^1637 ≤ 22300404521889^1637*1250000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675766977 1250000000 22300404521889 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2316119243/10000000000 : ℝ)^2149 ≤ (14658142132629/100000000000000 : ℝ)^1637 := by
    have hnat : (2316119243 : ℕ)^2149*100000000000000^1637 ≤ 14658142132629^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2316119243 10000000000 14658142132629 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5045941001/10000000000 : ℝ)^2149 ≤ (40741048813631/100000000000000 : ℝ)^1637 := by
    have hnat : (5045941001 : ℕ)^2149*100000000000000^1637 ≤ 40741048813631^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5045941001 10000000000 40741048813631 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675766977/1250000000 : ℝ), (-2316119243/10000000000 : ℝ), (5045941001/10000000000 : ℝ)] ![(22300404521889/50000000000000 : ℝ), (14658142132629/100000000000000 : ℝ), (40741048813631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675766977/1250000000 : ℝ)|^2149 ≤ (22300404521889/50000000000000 : ℝ)^1637
        have hw : |(675766977/1250000000 : ℝ)|=(675766977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2316119243/10000000000 : ℝ)|^2149 ≤ (14658142132629/100000000000000 : ℝ)^1637
        have hw : |(-2316119243/10000000000 : ℝ)|=(2316119243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5045941001/10000000000 : ℝ)|^2149 ≤ (40741048813631/100000000000000 : ℝ)^1637
        have hw : |(5045941001/10000000000 : ℝ)|=(5045941001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s1_2 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2703067921/5000000000 : ℝ)*x 0 + (5045940783/10000000000 : ℝ)*x 1 + (-2316119487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2703067921/5000000000 : ℝ)^2149 ≤ (44600809325367/100000000000000 : ℝ)^1637 := by
    have hnat : (2703067921 : ℕ)^2149*100000000000000^1637 ≤ 44600809325367^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703067921 5000000000 44600809325367 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5045940783/10000000000 : ℝ)^2149 ≤ (2037052325149/5000000000000 : ℝ)^1637 := by
    have hnat : (5045940783 : ℕ)^2149*5000000000000^1637 ≤ 2037052325149^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5045940783 10000000000 2037052325149 5000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2316119487/10000000000 : ℝ)^2149 ≤ (916134009989/6250000000000 : ℝ)^1637 := by
    have hnat : (2316119487 : ℕ)^2149*6250000000000^1637 ≤ 916134009989^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2316119487 10000000000 916134009989 6250000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2703067921/5000000000 : ℝ), (5045940783/10000000000 : ℝ), (-2316119487/10000000000 : ℝ)] ![(44600809325367/100000000000000 : ℝ), (2037052325149/5000000000000 : ℝ), (916134009989/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2703067921/5000000000 : ℝ)|^2149 ≤ (44600809325367/100000000000000 : ℝ)^1637
        have hw : |(2703067921/5000000000 : ℝ)|=(2703067921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5045940783/10000000000 : ℝ)|^2149 ≤ (2037052325149/5000000000000 : ℝ)^1637
        have hw : |(5045940783/10000000000 : ℝ)|=(5045940783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2316119487/10000000000 : ℝ)|^2149 ≤ (916134009989/6250000000000 : ℝ)^1637
        have hw : |(-2316119487/10000000000 : ℝ)|=(2316119487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s1_3 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (858603887/2000000000 : ℝ)*x 0 + (231873131/625000000 : ℝ)*x 1 + (4960628931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (858603887/2000000000 : ℝ)^2149 ≤ (8238404440211/25000000000000 : ℝ)^1637 := by
    have hnat : (858603887 : ℕ)^2149*25000000000000^1637 ≤ 8238404440211^1637*2000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858603887 2000000000 8238404440211 25000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (231873131/625000000 : ℝ)^2149 ≤ (5441436540247/20000000000000 : ℝ)^1637 := by
    have hnat : (231873131 : ℕ)^2149*20000000000000^1637 ≤ 5441436540247^1637*625000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231873131 625000000 5441436540247 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4960628931/10000000000 : ℝ)^2149 ≤ (1991959975841/5000000000000 : ℝ)^1637 := by
    have hnat : (4960628931 : ℕ)^2149*5000000000000^1637 ≤ 1991959975841^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4960628931 10000000000 1991959975841 5000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(858603887/2000000000 : ℝ), (231873131/625000000 : ℝ), (4960628931/10000000000 : ℝ)] ![(8238404440211/25000000000000 : ℝ), (5441436540247/20000000000000 : ℝ), (1991959975841/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(858603887/2000000000 : ℝ)|^2149 ≤ (8238404440211/25000000000000 : ℝ)^1637
        have hw : |(858603887/2000000000 : ℝ)|=(858603887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(231873131/625000000 : ℝ)|^2149 ≤ (5441436540247/20000000000000 : ℝ)^1637
        have hw : |(231873131/625000000 : ℝ)|=(231873131/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4960628931/10000000000 : ℝ)|^2149 ≤ (1991959975841/5000000000000 : ℝ)^1637
        have hw : |(4960628931/10000000000 : ℝ)|=(4960628931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s1_4 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-998724657/5000000000 : ℝ)*x 0 + (505346681/1000000000 : ℝ)*x 1 + (2818136441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (998724657/5000000000 : ℝ)^2149 ≤ (482778013753/4000000000000 : ℝ)^1637 := by
    have hnat : (998724657 : ℕ)^2149*4000000000000^1637 ≤ 482778013753^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998724657 5000000000 482778013753 4000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505346681/1000000000 : ℝ)^2149 ≤ (10205208956957/25000000000000 : ℝ)^1637 := by
    have hnat : (505346681 : ℕ)^2149*25000000000000^1637 ≤ 10205208956957^1637*1000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505346681 1000000000 10205208956957 25000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2818136441/5000000000 : ℝ)^2149 ≤ (23554856901891/50000000000000 : ℝ)^1637 := by
    have hnat : (2818136441 : ℕ)^2149*50000000000000^1637 ≤ 23554856901891^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2818136441 5000000000 23554856901891 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-998724657/5000000000 : ℝ), (505346681/1000000000 : ℝ), (2818136441/5000000000 : ℝ)] ![(482778013753/4000000000000 : ℝ), (10205208956957/25000000000000 : ℝ), (23554856901891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-998724657/5000000000 : ℝ)|^2149 ≤ (482778013753/4000000000000 : ℝ)^1637
        have hw : |(-998724657/5000000000 : ℝ)|=(998724657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(505346681/1000000000 : ℝ)|^2149 ≤ (10205208956957/25000000000000 : ℝ)^1637
        have hw : |(505346681/1000000000 : ℝ)|=(505346681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2818136441/5000000000 : ℝ)|^2149 ≤ (23554856901891/50000000000000 : ℝ)^1637
        have hw : |(2818136441/5000000000 : ℝ)|=(2818136441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s1_5 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5251016499/10000000000 : ℝ)*x 0 + (-172578781/1000000000 : ℝ)*x 1 + (352267011/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251016499/10000000000 : ℝ)^2149 ≤ (42928397135081/100000000000000 : ℝ)^1637 := by
    have hnat : (5251016499 : ℕ)^2149*100000000000000^1637 ≤ 42928397135081^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251016499 10000000000 42928397135081 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172578781/1000000000 : ℝ)^2149 ≤ (19456829673/195312500000 : ℝ)^1637 := by
    have hnat : (172578781 : ℕ)^2149*195312500000^1637 ≤ 19456829673^1637*1000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172578781 1000000000 19456829673 195312500000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352267011/625000000 : ℝ)^2149 ≤ (47109706057187/100000000000000 : ℝ)^1637 := by
    have hnat : (352267011 : ℕ)^2149*100000000000000^1637 ≤ 47109706057187^1637*625000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352267011 625000000 47109706057187 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251016499/10000000000 : ℝ), (-172578781/1000000000 : ℝ), (352267011/625000000 : ℝ)] ![(42928397135081/100000000000000 : ℝ), (19456829673/195312500000 : ℝ), (47109706057187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251016499/10000000000 : ℝ)|^2149 ≤ (42928397135081/100000000000000 : ℝ)^1637
        have hw : |(5251016499/10000000000 : ℝ)|=(5251016499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-172578781/1000000000 : ℝ)|^2149 ≤ (19456829673/195312500000 : ℝ)^1637
        have hw : |(-172578781/1000000000 : ℝ)|=(172578781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(352267011/625000000 : ℝ)|^2149 ≤ (47109706057187/100000000000000 : ℝ)^1637
        have hw : |(352267011/625000000 : ℝ)|=(352267011/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s1_6 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1312753971/2500000000 : ℝ)*x 0 + (5636271983/10000000000 : ℝ)*x 1 + (-10786181/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312753971/2500000000 : ℝ)^2149 ≤ (21464195267387/50000000000000 : ℝ)^1637 := by
    have hnat : (1312753971 : ℕ)^2149*50000000000000^1637 ≤ 21464195267387^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312753971 2500000000 21464195267387 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5636271983/10000000000 : ℝ)^2149 ≤ (11777425984873/25000000000000 : ℝ)^1637 := by
    have hnat : (5636271983 : ℕ)^2149*25000000000000^1637 ≤ 11777425984873^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5636271983 10000000000 11777425984873 25000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10786181/62500000 : ℝ)^2149 ≤ (1245238188379/12500000000000 : ℝ)^1637 := by
    have hnat : (10786181 : ℕ)^2149*12500000000000^1637 ≤ 1245238188379^1637*62500000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10786181 62500000 1245238188379 12500000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312753971/2500000000 : ℝ), (5636271983/10000000000 : ℝ), (-10786181/62500000 : ℝ)] ![(21464195267387/50000000000000 : ℝ), (11777425984873/25000000000000 : ℝ), (1245238188379/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312753971/2500000000 : ℝ)|^2149 ≤ (21464195267387/50000000000000 : ℝ)^1637
        have hw : |(1312753971/2500000000 : ℝ)|=(1312753971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5636271983/10000000000 : ℝ)|^2149 ≤ (11777425984873/25000000000000 : ℝ)^1637
        have hw : |(5636271983/10000000000 : ℝ)|=(5636271983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10786181/62500000 : ℝ)|^2149 ≤ (1245238188379/12500000000000 : ℝ)^1637
        have hw : |(-10786181/62500000 : ℝ)|=(10786181/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s1_7 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (42941561/100000000 : ℝ)*x 0 + (2472444243/5000000000 : ℝ)*x 1 + (232874909/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42941561/100000000 : ℝ)^2149 ≤ (32965072321853/100000000000000 : ℝ)^1637 := by
    have hnat : (42941561 : ℕ)^2149*100000000000000^1637 ≤ 32965072321853^1637*100000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42941561 100000000 32965072321853 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2472444243/5000000000 : ℝ)^2149 ≤ (39673331409367/100000000000000 : ℝ)^1637 := by
    have hnat : (2472444243 : ℕ)^2149*100000000000000^1637 ≤ 39673331409367^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2472444243 5000000000 39673331409367 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (232874909/625000000 : ℝ)^2149 ≤ (27361596251581/100000000000000 : ℝ)^1637 := by
    have hnat : (232874909 : ℕ)^2149*100000000000000^1637 ≤ 27361596251581^1637*625000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232874909 625000000 27361596251581 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42941561/100000000 : ℝ), (2472444243/5000000000 : ℝ), (232874909/625000000 : ℝ)] ![(32965072321853/100000000000000 : ℝ), (39673331409367/100000000000000 : ℝ), (27361596251581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42941561/100000000 : ℝ)|^2149 ≤ (32965072321853/100000000000000 : ℝ)^1637
        have hw : |(42941561/100000000 : ℝ)|=(42941561/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2472444243/5000000000 : ℝ)|^2149 ≤ (39673331409367/100000000000000 : ℝ)^1637
        have hw : |(2472444243/5000000000 : ℝ)|=(2472444243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(232874909/625000000 : ℝ)|^2149 ≤ (27361596251581/100000000000000 : ℝ)^1637
        have hw : |(232874909/625000000 : ℝ)|=(232874909/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1338_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (269/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (173/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1713/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4873/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (269/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (173/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (269/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (173/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (269/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (173/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (269/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (173/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (269/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (173/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (269/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (173/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (173/12500 : ℝ) ^ (4297/1024 : ℝ) ≤ (1583688292903/100000000000000000000 : ℝ) := by
    have hpowers : (173/12500 : ℝ)^4297 ≤ (1583688292903/100000000000000000000 : ℝ)^1024 := by
      have hnat : (173 : ℕ)^4297*100000000000000000000^1024 ≤ 1583688292903^1024*12500^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        173 12500 1583688292903 100000000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (173/12500 : ℝ)) (X := (1583688292903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (269/1000 : ℝ) ^ (4297/1024 : ℝ) ≤ (50580805669778541/12500000000000000000 : ℝ) := by
    have hpowers : (269/1000 : ℝ)^4297 ≤ (50580805669778541/12500000000000000000 : ℝ)^1024 := by
      have hnat : (269 : ℕ)^4297*12500000000000000000^1024 ≤ 50580805669778541^1024*1000^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        269 1000 50580805669778541 12500000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (269/1000 : ℝ)) (X := (50580805669778541/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000001583688292903/50000000000000000000 : ℝ) ≤ (10000000075480419/10000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (50000001583688292903/50000000000000000000 : ℝ)^1024 ≤ (10000000075480419/10000000000000000 : ℝ)^4297 := by
      have hnat : (50000001583688292903 : ℕ)^1024*10000000000000000^4297 ≤ 10000000075480419^4297*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000001583688292903 50000000000000000000 10000000075480419 10000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000075480419/10000000000000000 : ℝ)) (X := (50000001583688292903/50000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100404648029046521231/100000000000000000000 : ℝ) ≤ (10009628171500113/10000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (100404648029046521231/100000000000000000000 : ℝ)^1024 ≤ (10009628171500113/10000000000000000 : ℝ)^4297 := by
      have hnat : (100404648029046521231 : ℕ)^1024*10000000000000000^4297 ≤ 10009628171500113^4297*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100404648029046521231 100000000000000000000 10009628171500113 10000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009628171500113/10000000000000000 : ℝ)) (X := (100404648029046521231/100000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6300580805669778541/6250000000000000000 : ℝ) ≤ (10019256267519807/10000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (6300580805669778541/6250000000000000000 : ℝ)^1024 ≤ (10019256267519807/10000000000000000 : ℝ)^4297 := by
      have hnat : (6300580805669778541 : ℕ)^1024*10000000000000000^4297 ≤ 10019256267519807^4297*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6300580805669778541 6250000000000000000 10019256267519807 10000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10019256267519807/10000000000000000 : ℝ)) (X := (6300580805669778541/6250000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1583688292903/100000000000000000000 : ℝ) ≤ ((63783337839043964553/63790000000000000000 : ℝ)+2*(4814048009847/1275800000000000 : ℝ)*(173/12500 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (63783337839043964553/63790000000000000000 : ℝ)+2*(4814048009847/1275800000000000 : ℝ)*(173/12500 : ℝ)=(10000000075480419/10000000000000000 : ℝ) by norm_num, show 1+2*(1583688292903/100000000000000000000 : ℝ)=(50000001583688292903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(50580805669778541/12500000000000000000 : ℝ)+(1583688292903/100000000000000000000 : ℝ) ≤ ((63783337839043964553/63790000000000000000 : ℝ)+(4814048009847/1275800000000000 : ℝ)*((269/1000 : ℝ)+(173/12500 : ℝ)))^(4297/1024 : ℝ) := by
    rw [show (63783337839043964553/63790000000000000000 : ℝ)+(4814048009847/1275800000000000 : ℝ)*((269/1000 : ℝ)+(173/12500 : ℝ))=(10009628171500113/10000000000000000 : ℝ) by norm_num, show 1+(50580805669778541/12500000000000000000 : ℝ)+(1583688292903/100000000000000000000 : ℝ)=(100404648029046521231/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(50580805669778541/12500000000000000000 : ℝ) ≤ ((63783337839043964553/63790000000000000000 : ℝ)+2*(4814048009847/1275800000000000 : ℝ)*(269/1000 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (63783337839043964553/63790000000000000000 : ℝ)+2*(4814048009847/1275800000000000 : ℝ)*(269/1000 : ℝ)=(10019256267519807/10000000000000000 : ℝ) by norm_num, show 1+2*(50580805669778541/12500000000000000000 : ℝ)=(6300580805669778541/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (63783337839043964553/63790000000000000000 : ℝ)*(X 1 0+X 2 0)+(4814048009847/1275800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (173/12500 : ℝ)) (hi := (269/1000 : ℝ)) (c := (63783337839043964553/63790000000000000000 : ℝ)) (alpha := (4814048009847/1275800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (63783337839043964553/63790000000000000000 : ℝ)*(X 0 1+X 2 1)+(4814048009847/1275800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (173/12500 : ℝ)) (hi := (269/1000 : ℝ)) (c := (63783337839043964553/63790000000000000000 : ℝ)) (alpha := (4814048009847/1275800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (63783337839043964553/63790000000000000000 : ℝ)*(X 0 2+X 1 2)+(4814048009847/1275800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (173/12500 : ℝ)) (hi := (269/1000 : ℝ)) (c := (63783337839043964553/63790000000000000000 : ℝ)) (alpha := (4814048009847/1275800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-31201647/156250000 : ℝ)*X 0 0+(5643935843/10000000000 : ℝ)*X 0 1+(5045941137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((675766977/1250000000 : ℝ)*X 1 0+(-2316119243/10000000000 : ℝ)*X 1 1+(5045941001/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2703067921/5000000000 : ℝ)*X 2 0+(5045940783/10000000000 : ℝ)*X 2 1+(-2316119487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((858603887/2000000000 : ℝ)*X 0 0+(231873131/625000000 : ℝ)*X 0 1+(4960628931/10000000000 : ℝ)*X 0 2+(858603887/2000000000 : ℝ)*X 1 0+(231873131/625000000 : ℝ)*X 1 1+(4960628931/10000000000 : ℝ)*X 1 2+(858603887/2000000000 : ℝ)*X 2 0+(231873131/625000000 : ℝ)*X 2 1+(4960628931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-998724657/5000000000 : ℝ)*X 0 0+(505346681/1000000000 : ℝ)*X 0 1+(2818136441/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5251016499/10000000000 : ℝ)*X 1 0+(-172578781/1000000000 : ℝ)*X 1 1+(352267011/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1312753971/2500000000 : ℝ)*X 2 0+(5636271983/10000000000 : ℝ)*X 2 1+(-10786181/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((42941561/100000000 : ℝ)*X 0 0+(2472444243/5000000000 : ℝ)*X 0 1+(232874909/625000000 : ℝ)*X 0 2+(42941561/100000000 : ℝ)*X 1 0+(2472444243/5000000000 : ℝ)*X 1 1+(232874909/625000000 : ℝ)*X 1 2+(42941561/100000000 : ℝ)*X 2 0+(2472444243/5000000000 : ℝ)*X 2 1+(232874909/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (675083337708486358234149/63790000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15520547/12500000000000 : ℝ)*(base1) + (1807697627/100000000000000 : ℝ)*(base19) + (453935043/25000000000000 : ℝ)*(base23) + (137679987/50000000000000 : ℝ)*(upper3) + (44417311/25000000000000 : ℝ)*(upper5) + (1235931414675769/100000000000000 : ℝ)*(major0) + (1235931414675769/100000000000000 : ℝ)*(major1) + (1235931414675769/100000000000000 : ℝ)*(major2) + (836132763276187/50000000000000 : ℝ)*(sp0) + (1672272653809321/100000000000000 : ℝ)*(sp1) + (209034080720847/12500000000000 : ℝ)*(sp2) + (799582931454373/100000000000000 : ℝ)*(sp3) + (181182379/2000000000000 : ℝ)*(sp4) + (4959462427/100000000000000 : ℝ)*(sp7) + (99948501885147/12500000000000 : ℝ)*(f.failure) + (418068615376737/25000000000000 : ℝ)*(f.sum) + (103809830171427/63790000000000000000000000000 : ℝ)*base66 + (75067695625243166257/6379000000000000000000000000000000 : ℝ)*base67 + (11949254937439833743/6379000000000000000000000000000000 : ℝ)*base70 + (193553014002166257/6379000000000000000000000000000000 : ℝ)*base71 + (301280510448013/63790000000000000000000000000 : ℝ)*base73 + (6979677017796833743/6379000000000000000000000000000000 : ℝ)*base76 + (11588715029178166257/6379000000000000000000000000000000 : ℝ)*base77 + (13105616129810833743/6379000000000000000000000000000000 : ℝ)*base80 + (251442380994467/63790000000000000000000000000 : ℝ)*base82 + (694721/312500000000000000000 : ℝ)*base90 + (694721/312500000000000000000 : ℝ)*base92 + (694721/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (456853356978309255747292017/39868750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5007837/25000000000000 : ℝ)*(base1) + (927296643/50000000000000 : ℝ)*(base19) + (151556387/10000000000000 : ℝ)*(base23) + (13410663/10000000000000 : ℝ)*(upper3) + (291345239/100000000000000 : ℝ)*(upper5) + (31703194531437/2500000000000 : ℝ)*(major0) + (31703194531437/2500000000000 : ℝ)*(major1) + (31703194531437/2500000000000 : ℝ)*(major2) + (9194145107/100000000000000 : ℝ)*(sp1) + (2260120789/50000000000000 : ℝ)*(sp2) + (214479711148177/12500000000000 : ℝ)*(sp4) + (68633064816627/4000000000000 : ℝ)*(sp5) + (1715831633348619/100000000000000 : ℝ)*(sp6) + (410208745682541/50000000000000 : ℝ)*(sp7) + (82041751139643/10000000000000 : ℝ)*(f.failure) + (428959417288517/25000000000000 : ℝ)*(f.sum) + (797047940313/1594750000000000000000000000 : ℝ)*base65 + (221875915614597339/159475000000000000000000000000000 : ℝ)*base68 + (1266210712477102661/159475000000000000000000000000000 : ℝ)*base69 + (588562395286027661/159475000000000000000000000000000 : ℝ)*base71 + (24305518473723/6379000000000000000000000000 : ℝ)*base74 + (908842866824477661/159475000000000000000000000000000 : ℝ)*base75 + (1914464857771902661/159475000000000000000000000000000 : ℝ)*base77 + (1134957463723177661/159475000000000000000000000000000 : ℝ)*base79 + (4591370118639/3189500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2484249/250000000000000000000 : ℝ)*base90 + (2484249/250000000000000000000 : ℝ)*base92 + (2484249/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1338_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (269/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (173/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1713/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4873/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1338_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1338_s2_0 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-10187043/50000000 : ℝ)*x 0 + (685107237/1250000000 : ℝ)*x 1 + (1036616077/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10187043/50000000 : ℝ)^2149 ≤ (309685168853/2500000000000 : ℝ)^1637 := by
    have hnat : (10187043 : ℕ)^2149*2500000000000^1637 ≤ 309685168853^1637*50000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10187043 50000000 309685168853 2500000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685107237/1250000000 : ℝ)^2149 ≤ (45411820959189/100000000000000 : ℝ)^1637 := by
    have hnat : (685107237 : ℕ)^2149*100000000000000^1637 ≤ 45411820959189^1637*1250000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685107237 1250000000 45411820959189 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036616077/2000000000 : ℝ)^2149 ≤ (21100386137149/50000000000000 : ℝ)^1637 := by
    have hnat : (1036616077 : ℕ)^2149*50000000000000^1637 ≤ 21100386137149^1637*2000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036616077 2000000000 21100386137149 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10187043/50000000 : ℝ), (685107237/1250000000 : ℝ), (1036616077/2000000000 : ℝ)] ![(309685168853/2500000000000 : ℝ), (45411820959189/100000000000000 : ℝ), (21100386137149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10187043/50000000 : ℝ)|^2149 ≤ (309685168853/2500000000000 : ℝ)^1637
        have hw : |(-10187043/50000000 : ℝ)|=(10187043/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(685107237/1250000000 : ℝ)|^2149 ≤ (45411820959189/100000000000000 : ℝ)^1637
        have hw : |(685107237/1250000000 : ℝ)|=(685107237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036616077/2000000000 : ℝ)|^2149 ≤ (21100386137149/50000000000000 : ℝ)^1637
        have hw : |(1036616077/2000000000 : ℝ)|=(1036616077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s2_1 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (41923733/78125000 : ℝ)*x 0 + (-2191306529/10000000000 : ℝ)*x 1 + (518308077/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41923733/78125000 : ℝ)^2149 ≤ (22084599180119/50000000000000 : ℝ)^1637 := by
    have hnat : (41923733 : ℕ)^2149*50000000000000^1637 ≤ 22084599180119^1637*78125000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41923733 78125000 22084599180119 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2191306529/10000000000 : ℝ)^2149 ≤ (212969144281/1562500000000 : ℝ)^1637 := by
    have hnat : (2191306529 : ℕ)^2149*1562500000000^1637 ≤ 212969144281^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191306529 10000000000 212969144281 1562500000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518308077/1000000000 : ℝ)^2149 ≤ (42200776389403/100000000000000 : ℝ)^1637 := by
    have hnat : (518308077 : ℕ)^2149*100000000000000^1637 ≤ 42200776389403^1637*1000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518308077 1000000000 42200776389403 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41923733/78125000 : ℝ), (-2191306529/10000000000 : ℝ), (518308077/1000000000 : ℝ)] ![(22084599180119/50000000000000 : ℝ), (212969144281/1562500000000 : ℝ), (42200776389403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41923733/78125000 : ℝ)|^2149 ≤ (22084599180119/50000000000000 : ℝ)^1637
        have hw : |(41923733/78125000 : ℝ)|=(41923733/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2191306529/10000000000 : ℝ)|^2149 ≤ (212969144281/1562500000000 : ℝ)^1637
        have hw : |(-2191306529/10000000000 : ℝ)|=(2191306529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518308077/1000000000 : ℝ)|^2149 ≤ (42200776389403/100000000000000 : ℝ)^1637
        have hw : |(518308077/1000000000 : ℝ)|=(518308077/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s2_2 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (670779739/1250000000 : ℝ)*x 0 + (5183080667/10000000000 : ℝ)*x 1 + (-2191306547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670779739/1250000000 : ℝ)^2149 ≤ (8833839862221/20000000000000 : ℝ)^1637 := by
    have hnat : (670779739 : ℕ)^2149*20000000000000^1637 ≤ 8833839862221^1637*1250000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670779739 1250000000 8833839862221 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183080667/10000000000 : ℝ)^2149 ≤ (42200775288479/100000000000000 : ℝ)^1637 := by
    have hnat : (5183080667 : ℕ)^2149*100000000000000^1637 ≤ 42200775288479^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183080667 10000000000 42200775288479 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2191306547/10000000000 : ℝ)^2149 ≤ (6815012690481/50000000000000 : ℝ)^1637 := by
    have hnat : (2191306547 : ℕ)^2149*50000000000000^1637 ≤ 6815012690481^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191306547 10000000000 6815012690481 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670779739/1250000000 : ℝ), (5183080667/10000000000 : ℝ), (-2191306547/10000000000 : ℝ)] ![(8833839862221/20000000000000 : ℝ), (42200775288479/100000000000000 : ℝ), (6815012690481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670779739/1250000000 : ℝ)|^2149 ≤ (8833839862221/20000000000000 : ℝ)^1637
        have hw : |(670779739/1250000000 : ℝ)|=(670779739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183080667/10000000000 : ℝ)|^2149 ≤ (42200775288479/100000000000000 : ℝ)^1637
        have hw : |(5183080667/10000000000 : ℝ)|=(5183080667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2191306547/10000000000 : ℝ)|^2149 ≤ (6815012690481/50000000000000 : ℝ)^1637
        have hw : |(-2191306547/10000000000 : ℝ)|=(2191306547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s2_3 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2160664429/5000000000 : ℝ)*x 0 + (2010208631/5000000000 : ℝ)*x 1 + (290199659/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160664429/5000000000 : ℝ)^2149 ≤ (16619591702087/50000000000000 : ℝ)^1637 := by
    have hnat : (2160664429 : ℕ)^2149*50000000000000^1637 ≤ 16619591702087^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160664429 5000000000 16619591702087 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010208631/5000000000 : ℝ)^2149 ≤ (30234312348751/100000000000000 : ℝ)^1637 := by
    have hnat : (2010208631 : ℕ)^2149*100000000000000^1637 ≤ 30234312348751^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010208631 5000000000 30234312348751 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (290199659/625000000 : ℝ)^2149 ≤ (36526504226579/100000000000000 : ℝ)^1637 := by
    have hnat : (290199659 : ℕ)^2149*100000000000000^1637 ≤ 36526504226579^1637*625000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290199659 625000000 36526504226579 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160664429/5000000000 : ℝ), (2010208631/5000000000 : ℝ), (290199659/625000000 : ℝ)] ![(16619591702087/50000000000000 : ℝ), (30234312348751/100000000000000 : ℝ), (36526504226579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160664429/5000000000 : ℝ)|^2149 ≤ (16619591702087/50000000000000 : ℝ)^1637
        have hw : |(2160664429/5000000000 : ℝ)|=(2160664429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2010208631/5000000000 : ℝ)|^2149 ≤ (30234312348751/100000000000000 : ℝ)^1637
        have hw : |(2010208631/5000000000 : ℝ)|=(2010208631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(290199659/625000000 : ℝ)|^2149 ≤ (36526504226579/100000000000000 : ℝ)^1637
        have hw : |(290199659/625000000 : ℝ)|=(290199659/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s2_4 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-407495153/2000000000 : ℝ)*x 0 + (2592478463/5000000000 : ℝ)*x 1 + (1369741091/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (407495153/2000000000 : ℝ)^2149 ≤ (12387942841097/100000000000000 : ℝ)^1637 := by
    have hnat : (407495153 : ℕ)^2149*100000000000000^1637 ≤ 12387942841097^1637*2000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407495153 2000000000 12387942841097 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592478463/5000000000 : ℝ)^2149 ≤ (1319400968021/3125000000000 : ℝ)^1637 := by
    have hnat : (2592478463 : ℕ)^2149*3125000000000^1637 ≤ 1319400968021^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592478463 5000000000 1319400968021 3125000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369741091/2500000000 : ℝ)^2149 ≤ (567390327159/1250000000000 : ℝ)^1637 := by
    have hnat : (1369741091 : ℕ)^2149*1250000000000^1637 ≤ 567390327159^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369741091 2500000000 567390327159 1250000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-407495153/2000000000 : ℝ), (2592478463/5000000000 : ℝ), (1369741091/2500000000 : ℝ)] ![(12387942841097/100000000000000 : ℝ), (1319400968021/3125000000000 : ℝ), (567390327159/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-407495153/2000000000 : ℝ)|^2149 ≤ (12387942841097/100000000000000 : ℝ)^1637
        have hw : |(-407495153/2000000000 : ℝ)|=(407495153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592478463/5000000000 : ℝ)|^2149 ≤ (1319400968021/3125000000000 : ℝ)^1637
        have hw : |(2592478463/5000000000 : ℝ)|=(2592478463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369741091/2500000000 : ℝ)|^2149 ≤ (567390327159/1250000000000 : ℝ)^1637
        have hw : |(1369741091/2500000000 : ℝ)|=(1369741091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s2_5 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (66118989/125000000 : ℝ)*x 0 + (-473855659/2500000000 : ℝ)*x 1 + (8766343/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66118989/125000000 : ℝ)^2149 ≤ (8668417650219/20000000000000 : ℝ)^1637 := by
    have hnat : (66118989 : ℕ)^2149*20000000000000^1637 ≤ 8668417650219^1637*125000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66118989 125000000 8668417650219 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (473855659/2500000000 : ℝ)^2149 ≤ (5633342720743/50000000000000 : ℝ)^1637 := by
    have hnat : (473855659 : ℕ)^2149*50000000000000^1637 ≤ 5633342720743^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473855659 2500000000 5633342720743 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8766343/16000000 : ℝ)^2149 ≤ (45391226292353/100000000000000 : ℝ)^1637 := by
    have hnat : (8766343 : ℕ)^2149*100000000000000^1637 ≤ 45391226292353^1637*16000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8766343 16000000 45391226292353 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66118989/125000000 : ℝ), (-473855659/2500000000 : ℝ), (8766343/16000000 : ℝ)] ![(8668417650219/20000000000000 : ℝ), (5633342720743/50000000000000 : ℝ), (45391226292353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66118989/125000000 : ℝ)|^2149 ≤ (8668417650219/20000000000000 : ℝ)^1637
        have hw : |(66118989/125000000 : ℝ)|=(66118989/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-473855659/2500000000 : ℝ)|^2149 ≤ (5633342720743/50000000000000 : ℝ)^1637
        have hw : |(-473855659/2500000000 : ℝ)|=(473855659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8766343/16000000 : ℝ)|^2149 ≤ (45391226292353/100000000000000 : ℝ)^1637
        have hw : |(8766343/16000000 : ℝ)|=(8766343/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s2_6 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5289519149/10000000000 : ℝ)*x 0 + (5478964371/10000000000 : ℝ)*x 1 + (-947711301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289519149/10000000000 : ℝ)^2149 ≤ (43342088563041/100000000000000 : ℝ)^1637 := by
    have hnat : (5289519149 : ℕ)^2149*100000000000000^1637 ≤ 43342088563041^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289519149 10000000000 43342088563041 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5478964371/10000000000 : ℝ)^2149 ≤ (907824524977/2000000000000 : ℝ)^1637 := by
    have hnat : (5478964371 : ℕ)^2149*2000000000000^1637 ≤ 907824524977^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478964371 10000000000 907824524977 2000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (947711301/5000000000 : ℝ)^2149 ≤ (5633342588087/50000000000000 : ℝ)^1637 := by
    have hnat : (947711301 : ℕ)^2149*50000000000000^1637 ≤ 5633342588087^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947711301 5000000000 5633342588087 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289519149/10000000000 : ℝ), (5478964371/10000000000 : ℝ), (-947711301/5000000000 : ℝ)] ![(43342088563041/100000000000000 : ℝ), (907824524977/2000000000000 : ℝ), (5633342588087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289519149/10000000000 : ℝ)|^2149 ≤ (43342088563041/100000000000000 : ℝ)^1637
        have hw : |(5289519149/10000000000 : ℝ)|=(5289519149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5478964371/10000000000 : ℝ)|^2149 ≤ (907824524977/2000000000000 : ℝ)^1637
        have hw : |(5478964371/10000000000 : ℝ)|=(5478964371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-947711301/5000000000 : ℝ)|^2149 ≤ (5633342588087/50000000000000 : ℝ)^1637
        have hw : |(-947711301/5000000000 : ℝ)|=(947711301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s2_7 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2160734847/5000000000 : ℝ)*x 0 + (2319635289/5000000000 : ℝ)*x 1 + (251523551/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160734847/5000000000 : ℝ)^2149 ≤ (16620302762767/50000000000000 : ℝ)^1637 := by
    have hnat : (2160734847 : ℕ)^2149*50000000000000^1637 ≤ 16620302762767^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160734847 5000000000 16620302762767 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2319635289/5000000000 : ℝ)^2149 ≤ (18242993169733/50000000000000 : ℝ)^1637 := by
    have hnat : (2319635289 : ℕ)^2149*50000000000000^1637 ≤ 18242993169733^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2319635289 5000000000 18242993169733 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251523551/625000000 : ℝ)^2149 ≤ (15136704062517/50000000000000 : ℝ)^1637 := by
    have hnat : (251523551 : ℕ)^2149*50000000000000^1637 ≤ 15136704062517^1637*625000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251523551 625000000 15136704062517 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160734847/5000000000 : ℝ), (2319635289/5000000000 : ℝ), (251523551/625000000 : ℝ)] ![(16620302762767/50000000000000 : ℝ), (18242993169733/50000000000000 : ℝ), (15136704062517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160734847/5000000000 : ℝ)|^2149 ≤ (16620302762767/50000000000000 : ℝ)^1637
        have hw : |(2160734847/5000000000 : ℝ)|=(2160734847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2319635289/5000000000 : ℝ)|^2149 ≤ (18242993169733/50000000000000 : ℝ)^1637
        have hw : |(2319635289/5000000000 : ℝ)|=(2319635289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251523551/625000000 : ℝ)|^2149 ≤ (15136704062517/50000000000000 : ℝ)^1637
        have hw : |(251523551/625000000 : ℝ)|=(251523551/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1338_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4873/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1713/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (393/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (403/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4873/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1713/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4873/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1713/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4873/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1713/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4873/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1713/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4873/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1713/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4873/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1713/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1713/25000 : ℝ) ^ (4297/1024 : ℝ) ≤ (1302426119139463/100000000000000000000 : ℝ) := by
    have hpowers : (1713/25000 : ℝ)^4297 ≤ (1302426119139463/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1713 : ℕ)^4297*100000000000000000000^1024 ≤ 1302426119139463^1024*25000^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1713 25000 1302426119139463 100000000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1713/25000 : ℝ)) (X := (1302426119139463/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4873/25000 : ℝ) ^ (4297/1024 : ℝ) ≤ (26180154101023153/25000000000000000000 : ℝ) := by
    have hpowers : (4873/25000 : ℝ)^4297 ≤ (26180154101023153/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4873 : ℕ)^4297*25000000000000000000^1024 ≤ 26180154101023153^1024*25000^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4873 25000 26180154101023153 25000000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4873/25000 : ℝ)) (X := (26180154101023153/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001302426119139463/50000000000000000000 : ℝ) ≤ (2500015518630619/2500000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (50001302426119139463/50000000000000000000 : ℝ)^1024 ≤ (2500015518630619/2500000000000000 : ℝ)^4297 := by
      have hnat : (50001302426119139463 : ℕ)^1024*2500000000000000^4297 ≤ 2500015518630619^4297*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001302426119139463 50000000000000000000 2500015518630619 2500000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500015518630619/2500000000000000 : ℝ)) (X := (50001302426119139463/50000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4004240921700929283/4000000000000000000 : ℝ) ≤ (10002525570974551/10000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (4004240921700929283/4000000000000000000 : ℝ)^1024 ≤ (10002525570974551/10000000000000000 : ℝ)^4297 := by
      have hnat : (4004240921700929283 : ℕ)^1024*10000000000000000^4297 ≤ 10002525570974551^4297*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4004240921700929283 4000000000000000000 10002525570974551 10000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002525570974551/10000000000000000 : ℝ)) (X := (4004240921700929283/4000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12526180154101023153/12500000000000000000 : ℝ) ≤ (5002494533713313/5000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (12526180154101023153/12500000000000000000 : ℝ)^1024 ≤ (5002494533713313/5000000000000000 : ℝ)^4297 := by
      have hnat : (12526180154101023153 : ℕ)^1024*5000000000000000^4297 ≤ 5002494533713313^4297*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12526180154101023153 12500000000000000000 5002494533713313 5000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002494533713313/5000000000000000 : ℝ)) (X := (12526180154101023153/12500000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1302426119139463/100000000000000000000 : ℝ) ≤ ((3159175621664621521/3160000000000000000 : ℝ)+2*(98539858083/50560000000000 : ℝ)*(1713/25000 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (3159175621664621521/3160000000000000000 : ℝ)+2*(98539858083/50560000000000 : ℝ)*(1713/25000 : ℝ)=(2500015518630619/2500000000000000 : ℝ) by norm_num, show 1+2*(1302426119139463/100000000000000000000 : ℝ)=(50001302426119139463/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26180154101023153/25000000000000000000 : ℝ)+(1302426119139463/100000000000000000000 : ℝ) ≤ ((3159175621664621521/3160000000000000000 : ℝ)+(98539858083/50560000000000 : ℝ)*((4873/25000 : ℝ)+(1713/25000 : ℝ)))^(4297/1024 : ℝ) := by
    rw [show (3159175621664621521/3160000000000000000 : ℝ)+(98539858083/50560000000000 : ℝ)*((4873/25000 : ℝ)+(1713/25000 : ℝ))=(10002525570974551/10000000000000000 : ℝ) by norm_num, show 1+(26180154101023153/25000000000000000000 : ℝ)+(1302426119139463/100000000000000000000 : ℝ)=(4004240921700929283/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26180154101023153/25000000000000000000 : ℝ) ≤ ((3159175621664621521/3160000000000000000 : ℝ)+2*(98539858083/50560000000000 : ℝ)*(4873/25000 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (3159175621664621521/3160000000000000000 : ℝ)+2*(98539858083/50560000000000 : ℝ)*(4873/25000 : ℝ)=(5002494533713313/5000000000000000 : ℝ) by norm_num, show 1+2*(26180154101023153/25000000000000000000 : ℝ)=(12526180154101023153/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3159175621664621521/3160000000000000000 : ℝ)*(X 1 0+X 2 0)+(98539858083/50560000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (1713/25000 : ℝ)) (hi := (4873/25000 : ℝ)) (c := (3159175621664621521/3160000000000000000 : ℝ)) (alpha := (98539858083/50560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3159175621664621521/3160000000000000000 : ℝ)*(X 0 1+X 2 1)+(98539858083/50560000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (1713/25000 : ℝ)) (hi := (4873/25000 : ℝ)) (c := (3159175621664621521/3160000000000000000 : ℝ)) (alpha := (98539858083/50560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3159175621664621521/3160000000000000000 : ℝ)*(X 0 2+X 1 2)+(98539858083/50560000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (1713/25000 : ℝ)) (hi := (4873/25000 : ℝ)) (c := (3159175621664621521/3160000000000000000 : ℝ)) (alpha := (98539858083/50560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-10187043/50000000 : ℝ)*X 0 0+(685107237/1250000000 : ℝ)*X 0 1+(1036616077/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((41923733/78125000 : ℝ)*X 1 0+(-2191306529/10000000000 : ℝ)*X 1 1+(518308077/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((670779739/1250000000 : ℝ)*X 2 0+(5183080667/10000000000 : ℝ)*X 2 1+(-2191306547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2160664429/5000000000 : ℝ)*X 0 0+(2010208631/5000000000 : ℝ)*X 0 1+(290199659/625000000 : ℝ)*X 0 2+(2160664429/5000000000 : ℝ)*X 1 0+(2010208631/5000000000 : ℝ)*X 1 1+(290199659/625000000 : ℝ)*X 1 2+(2160664429/5000000000 : ℝ)*X 2 0+(2010208631/5000000000 : ℝ)*X 2 1+(290199659/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-407495153/2000000000 : ℝ)*X 0 0+(2592478463/5000000000 : ℝ)*X 0 1+(1369741091/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66118989/125000000 : ℝ)*X 1 0+(-473855659/2500000000 : ℝ)*X 1 1+(8766343/16000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289519149/10000000000 : ℝ)*X 2 0+(5478964371/10000000000 : ℝ)*X 2 1+(-947711301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2160734847/5000000000 : ℝ)*X 0 0+(2319635289/5000000000 : ℝ)*X 0 1+(251523551/625000000 : ℝ)*X 0 2+(2160734847/5000000000 : ℝ)*X 1 0+(2319635289/5000000000 : ℝ)*X 1 1+(251523551/625000000 : ℝ)*X 1 2+(2160734847/5000000000 : ℝ)*X 2 0+(2319635289/5000000000 : ℝ)*X 2 1+(251523551/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8473461838727285207993829/987500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1534308257/100000000000000 : ℝ)*(base19) + (76981727/5000000000000 : ℝ)*(base23) + (6673609/25000000000000 : ℝ)*(lower2) + (206904451/100000000000000 : ℝ)*(upper3) + (163339827/100000000000000 : ℝ)*(upper5) + (15512460068239/625000000000 : ℝ)*(major0) + (15512460068239/625000000000 : ℝ)*(major1) + (15512460068239/625000000000 : ℝ)*(major2) + (3358234423469321/100000000000000 : ℝ)*(sp0) + (671651048857191/20000000000000 : ℝ)*(sp1) + (419781904869959/12500000000000 : ℝ)*(sp2) + (160571993656467/10000000000000 : ℝ)*(sp3) + (22355124891/100000000000000 : ℝ)*(sp4) + (10220653563/100000000000000 : ℝ)*(sp7) + (802865078609117/50000000000000 : ℝ)*(f.failure) + (839564194648553/25000000000000 : ℝ)*(f.sum) + (46344372601/9875000000000000000000000 : ℝ)*base66 + (3589447276684019/1975000000000000000000000000000 : ℝ)*base67 + (10141801758709019/1975000000000000000000000000000 : ℝ)*base69 + (12949620341334019/1975000000000000000000000000000 : ℝ)*base71 + (7239998597/9875000000000000000000000 : ℝ)*base74 + (22270607687734019/1975000000000000000000000000000 : ℝ)*base75 + (13477887526934019/1975000000000000000000000000000 : ℝ)*base77 + (3127677381234019/1975000000000000000000000000000 : ℝ)*base79 + (260158451831/79000000000000000000000000 : ℝ)*base82 + (6215569/1250000000000000000000 : ℝ)*base89 + (6215569/1250000000000000000000 : ℝ)*base91 + (6215569/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (394222922179647153905144037/79000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1055905361/100000000000000 : ℝ)*(base19) + (1235523749/100000000000000 : ℝ)*(base23) + (137505137/100000000000000 : ℝ)*(upper3) + (61392457/100000000000000 : ℝ)*(lower4) + (15132323/25000000000000 : ℝ)*(upper5) + (1256892535192199/50000000000000 : ℝ)*(major0) + (1256892535192199/50000000000000 : ℝ)*(major1) + (1256892535192199/50000000000000 : ℝ)*(major2) + (11613175983/100000000000000 : ℝ)*(sp1) + (7354662897/50000000000000 : ℝ)*(sp2) + (1700636138135601/50000000000000 : ℝ)*(sp4) + (1700629803594929/50000000000000 : ℝ)*(sp5) + (1700628165710829/50000000000000 : ℝ)*(sp6) + (813148849079401/50000000000000 : ℝ)*(sp7) + (813148849079401/50000000000000 : ℝ)*(f.failure) + (1700636138135601/50000000000000 : ℝ)*(f.sum) + (81896178641/252800000000000000000000000 : ℝ)*base65 + (651598914329972821/158000000000000000000000000000000 : ℝ)*base68 + (125207275945972821/158000000000000000000000000000000 : ℝ)*base70 + (87892823585972821/158000000000000000000000000000000 : ℝ)*base72 + (2009412905787/1264000000000000000000000000 : ℝ)*base74 + (662250876801972821/158000000000000000000000000000000 : ℝ)*base76 + (543701871970027179/158000000000000000000000000000000 : ℝ)*base77 + (109751472758027179/158000000000000000000000000000000 : ℝ)*base79 + (804519937809/252800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (8451443/1250000000000000000000 : ℝ)*base90 + (8451443/1250000000000000000000 : ℝ)*base92 + (8451443/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1338_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4873/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1713/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (393/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (403/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1338_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1338_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (393/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (403/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1338_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1338_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1338_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (393/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (403/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1338_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

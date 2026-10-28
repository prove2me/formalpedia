-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1182_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:50:10.025296+00:00
-- url     : https://prove2.me/submissions/28e4557b-0cdb-4a16-9aae-791cd06b78e0

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
theorem support_rectangle_w1182_s6_0 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-429575651/2000000000 : ℝ)*x 0 + (2696289933/5000000000 : ℝ)*x 1 + (526610579/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429575651/2000000000 : ℝ)^8375 ≤ (13055288003589/100000000000000 : ℝ)^6327 := by
    have hnat : (429575651 : ℕ)^8375*100000000000000^6327 ≤ 13055288003589^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429575651 2000000000 13055288003589 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696289933/5000000000 : ℝ)^8375 ≤ (22077569486809/50000000000000 : ℝ)^6327 := by
    have hnat : (2696289933 : ℕ)^8375*50000000000000^6327 ≤ 22077569486809^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696289933 5000000000 22077569486809 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526610579/1000000000 : ℝ)^8375 ≤ (4278957300763/10000000000000 : ℝ)^6327 := by
    have hnat : (526610579 : ℕ)^8375*10000000000000^6327 ≤ 4278957300763^6327*1000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526610579 1000000000 4278957300763 10000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429575651/2000000000 : ℝ), (2696289933/5000000000 : ℝ), (526610579/1000000000 : ℝ)] ![(13055288003589/100000000000000 : ℝ), (22077569486809/50000000000000 : ℝ), (4278957300763/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429575651/2000000000 : ℝ)|^8375 ≤ (13055288003589/100000000000000 : ℝ)^6327
        have hw : |(-429575651/2000000000 : ℝ)|=(429575651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696289933/5000000000 : ℝ)|^8375 ≤ (22077569486809/50000000000000 : ℝ)^6327
        have hw : |(2696289933/5000000000 : ℝ)|=(2696289933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526610579/1000000000 : ℝ)|^8375 ≤ (4278957300763/10000000000000 : ℝ)^6327
        have hw : |(526610579/1000000000 : ℝ)|=(526610579/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s6_1 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344666823/10000000000 : ℝ)*x 0 + (-6912569/31250000 : ℝ)*x 1 + (1053221167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344666823/10000000000 : ℝ)^8375 ≤ (43636578771887/100000000000000 : ℝ)^6327 := by
    have hnat : (5344666823 : ℕ)^8375*100000000000000^6327 ≤ 43636578771887^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344666823 10000000000 43636578771887 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6912569/31250000 : ℝ)^8375 ≤ (3393461930037/25000000000000 : ℝ)^6327 := by
    have hnat : (6912569 : ℕ)^8375*25000000000000^6327 ≤ 3393461930037^6327*31250000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6912569 31250000 3393461930037 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053221167/2000000000 : ℝ)^8375 ≤ (42789573491633/100000000000000 : ℝ)^6327 := by
    have hnat : (1053221167 : ℕ)^8375*100000000000000^6327 ≤ 42789573491633^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053221167 2000000000 42789573491633 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344666823/10000000000 : ℝ), (-6912569/31250000 : ℝ), (1053221167/2000000000 : ℝ)] ![(43636578771887/100000000000000 : ℝ), (3393461930037/25000000000000 : ℝ), (42789573491633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344666823/10000000000 : ℝ)|^8375 ≤ (43636578771887/100000000000000 : ℝ)^6327
        have hw : |(5344666823/10000000000 : ℝ)|=(5344666823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6912569/31250000 : ℝ)|^8375 ≤ (3393461930037/25000000000000 : ℝ)^6327
        have hw : |(-6912569/31250000 : ℝ)|=(6912569/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053221167/2000000000 : ℝ)|^8375 ≤ (42789573491633/100000000000000 : ℝ)^6327
        have hw : |(1053221167/2000000000 : ℝ)|=(1053221167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s6_2 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068933383/2000000000 : ℝ)*x 0 + (5266105679/10000000000 : ℝ)*x 1 + (-442404433/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068933383/2000000000 : ℝ)^8375 ≤ (21818289883079/50000000000000 : ℝ)^6327 := by
    have hnat : (1068933383 : ℕ)^8375*50000000000000^6327 ≤ 21818289883079^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068933383 2000000000 21818289883079 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266105679/10000000000 : ℝ)^8375 ≤ (42789571813757/100000000000000 : ℝ)^6327 := by
    have hnat : (5266105679 : ℕ)^8375*100000000000000^6327 ≤ 42789571813757^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266105679 10000000000 42789571813757 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442404433/2000000000 : ℝ)^8375 ≤ (6786924205289/50000000000000 : ℝ)^6327 := by
    have hnat : (442404433 : ℕ)^8375*50000000000000^6327 ≤ 6786924205289^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442404433 2000000000 6786924205289 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068933383/2000000000 : ℝ), (5266105679/10000000000 : ℝ), (-442404433/2000000000 : ℝ)] ![(21818289883079/50000000000000 : ℝ), (42789571813757/100000000000000 : ℝ), (6786924205289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068933383/2000000000 : ℝ)|^8375 ≤ (21818289883079/50000000000000 : ℝ)^6327
        have hw : |(1068933383/2000000000 : ℝ)|=(1068933383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266105679/10000000000 : ℝ)|^8375 ≤ (42789571813757/100000000000000 : ℝ)^6327
        have hw : |(5266105679/10000000000 : ℝ)|=(5266105679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-442404433/2000000000 : ℝ)|^8375 ≤ (6786924205289/50000000000000 : ℝ)^6327
        have hw : |(-442404433/2000000000 : ℝ)|=(442404433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s6_3 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179527501/5000000000 : ℝ)*x 0 + (529259533/1250000000 : ℝ)*x 1 + (28047933/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179527501/5000000000 : ℝ)^8375 ≤ (33317046604087/100000000000000 : ℝ)^6327 := by
    have hnat : (2179527501 : ℕ)^8375*100000000000000^6327 ≤ 33317046604087^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179527501 5000000000 33317046604087 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529259533/1250000000 : ℝ)^8375 ≤ (32058515158651/100000000000000 : ℝ)^6327 := by
    have hnat : (529259533 : ℕ)^8375*100000000000000^6327 ≤ 32058515158651^6327*1250000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529259533 1250000000 32058515158651 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28047933/62500000 : ℝ)^8375 ≤ (34624438212603/100000000000000 : ℝ)^6327 := by
    have hnat : (28047933 : ℕ)^8375*100000000000000^6327 ≤ 34624438212603^6327*62500000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28047933 62500000 34624438212603 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179527501/5000000000 : ℝ), (529259533/1250000000 : ℝ), (28047933/62500000 : ℝ)] ![(33317046604087/100000000000000 : ℝ), (32058515158651/100000000000000 : ℝ), (34624438212603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179527501/5000000000 : ℝ)|^8375 ≤ (33317046604087/100000000000000 : ℝ)^6327
        have hw : |(2179527501/5000000000 : ℝ)|=(2179527501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(529259533/1250000000 : ℝ)|^8375 ≤ (32058515158651/100000000000000 : ℝ)^6327
        have hw : |(529259533/1250000000 : ℝ)|=(529259533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28047933/62500000 : ℝ)|^8375 ≤ (34624438212603/100000000000000 : ℝ)^6327
        have hw : |(28047933/62500000 : ℝ)|=(28047933/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s6_4 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2147883169/10000000000 : ℝ)*x 0 + (21065701/40000000 : ℝ)*x 1 + (5392259197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147883169/10000000000 : ℝ)^8375 ≤ (1631915942521/12500000000000 : ℝ)^6327 := by
    have hnat : (2147883169 : ℕ)^8375*12500000000000^6327 ≤ 1631915942521^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147883169 10000000000 1631915942521 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21065701/40000000 : ℝ)^8375 ≤ (1711720361239/4000000000000 : ℝ)^6327 := by
    have hnat : (21065701 : ℕ)^8375*4000000000000^6327 ≤ 1711720361239^6327*40000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21065701 40000000 1711720361239 4000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392259197/10000000000 : ℝ)^8375 ≤ (44151663416349/100000000000000 : ℝ)^6327 := by
    have hnat : (5392259197 : ℕ)^8375*100000000000000^6327 ≤ 44151663416349^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392259197 10000000000 44151663416349 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2147883169/10000000000 : ℝ), (21065701/40000000 : ℝ), (5392259197/10000000000 : ℝ)] ![(1631915942521/12500000000000 : ℝ), (1711720361239/4000000000000 : ℝ), (44151663416349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2147883169/10000000000 : ℝ)|^8375 ≤ (1631915942521/12500000000000 : ℝ)^6327
        have hw : |(-2147883169/10000000000 : ℝ)|=(2147883169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21065701/40000000 : ℝ)|^8375 ≤ (1711720361239/4000000000000 : ℝ)^6327
        have hw : |(21065701/40000000 : ℝ)|=(21065701/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392259197/10000000000 : ℝ)|^8375 ≤ (44151663416349/100000000000000 : ℝ)^6327
        have hw : |(5392259197/10000000000 : ℝ)|=(5392259197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s6_5 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312530723/10000000000 : ℝ)*x 0 + (-521467157/2500000000 : ℝ)*x 1 + (5392259193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312530723/10000000000 : ℝ)^8375 ≤ (43289612868689/100000000000000 : ℝ)^6327 := by
    have hnat : (5312530723 : ℕ)^8375*100000000000000^6327 ≤ 43289612868689^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312530723 10000000000 43289612868689 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521467157/2500000000 : ℝ)^8375 ≤ (6279361872899/50000000000000 : ℝ)^6327 := by
    have hnat : (521467157 : ℕ)^8375*50000000000000^6327 ≤ 6279361872899^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521467157 2500000000 6279361872899 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392259193/10000000000 : ℝ)^8375 ≤ (11037915843249/25000000000000 : ℝ)^6327 := by
    have hnat : (5392259193 : ℕ)^8375*25000000000000^6327 ≤ 11037915843249^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392259193 10000000000 11037915843249 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312530723/10000000000 : ℝ), (-521467157/2500000000 : ℝ), (5392259193/10000000000 : ℝ)] ![(43289612868689/100000000000000 : ℝ), (6279361872899/50000000000000 : ℝ), (11037915843249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312530723/10000000000 : ℝ)|^8375 ≤ (43289612868689/100000000000000 : ℝ)^6327
        have hw : |(5312530723/10000000000 : ℝ)|=(5312530723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-521467157/2500000000 : ℝ)|^8375 ≤ (6279361872899/50000000000000 : ℝ)^6327
        have hw : |(-521467157/2500000000 : ℝ)|=(521467157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392259193/10000000000 : ℝ)|^8375 ≤ (11037915843249/25000000000000 : ℝ)^6327
        have hw : |(5392259193/10000000000 : ℝ)|=(5392259193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s6_6 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312530719/10000000000 : ℝ)*x 0 + (1348064799/2500000000 : ℝ)*x 1 + (-2085868629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312530719/10000000000 : ℝ)^8375 ≤ (5411201603193/12500000000000 : ℝ)^6327 := by
    have hnat : (5312530719 : ℕ)^8375*12500000000000^6327 ≤ 5411201603193^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312530719 10000000000 5411201603193 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348064799/2500000000 : ℝ)^8375 ≤ (44151663405511/100000000000000 : ℝ)^6327 := by
    have hnat : (1348064799 : ℕ)^8375*100000000000000^6327 ≤ 44151663405511^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348064799 2500000000 44151663405511 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085868629/10000000000 : ℝ)^8375 ≤ (1569840469221/12500000000000 : ℝ)^6327 := by
    have hnat : (2085868629 : ℕ)^8375*12500000000000^6327 ≤ 1569840469221^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085868629 10000000000 1569840469221 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312530719/10000000000 : ℝ), (1348064799/2500000000 : ℝ), (-2085868629/10000000000 : ℝ)] ![(5411201603193/12500000000000 : ℝ), (44151663405511/100000000000000 : ℝ), (1569840469221/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312530719/10000000000 : ℝ)|^8375 ≤ (5411201603193/12500000000000 : ℝ)^6327
        have hw : |(5312530719/10000000000 : ℝ)|=(5312530719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348064799/2500000000 : ℝ)|^8375 ≤ (44151663405511/100000000000000 : ℝ)^6327
        have hw : |(1348064799/2500000000 : ℝ)|=(1348064799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2085868629/10000000000 : ℝ)|^8375 ≤ (1569840469221/12500000000000 : ℝ)^6327
        have hw : |(-2085868629/10000000000 : ℝ)|=(2085868629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s6_7 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089766141/2500000000 : ℝ)*x 0 + (4487028531/10000000000 : ℝ)*x 1 + (4234719509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089766141/2500000000 : ℝ)^8375 ≤ (6663428668993/20000000000000 : ℝ)^6327 := by
    have hnat : (1089766141 : ℕ)^8375*20000000000000^6327 ≤ 6663428668993^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089766141 2500000000 6663428668993 20000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487028531/10000000000 : ℝ)^8375 ≤ (17308947230739/50000000000000 : ℝ)^6327 := by
    have hnat : (4487028531 : ℕ)^8375*50000000000000^6327 ≤ 17308947230739^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487028531 10000000000 17308947230739 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4234719509/10000000000 : ℝ)^8375 ≤ (32064962175503/100000000000000 : ℝ)^6327 := by
    have hnat : (4234719509 : ℕ)^8375*100000000000000^6327 ≤ 32064962175503^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234719509 10000000000 32064962175503 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089766141/2500000000 : ℝ), (4487028531/10000000000 : ℝ), (4234719509/10000000000 : ℝ)] ![(6663428668993/20000000000000 : ℝ), (17308947230739/50000000000000 : ℝ), (32064962175503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089766141/2500000000 : ℝ)|^8375 ≤ (6663428668993/20000000000000 : ℝ)^6327
        have hw : |(1089766141/2500000000 : ℝ)|=(1089766141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487028531/10000000000 : ℝ)|^8375 ≤ (17308947230739/50000000000000 : ℝ)^6327
        have hw : |(4487028531/10000000000 : ℝ)|=(4487028531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4234719509/10000000000 : ℝ)|^8375 ≤ (32064962175503/100000000000000 : ℝ)^6327
        have hw : |(4234719509/10000000000 : ℝ)|=(4234719509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1182_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11399/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7039/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2821/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2821/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2821/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2821/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2821/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2821/20000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (11373/100000 : ℝ) ^ (4187/1024 : ℝ) ≤ (1723885591081861/12500000000000000000 : ℝ) := by
    have hpowers : (11373/100000 : ℝ)^4187 ≤ (1723885591081861/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11373 : ℕ)^4187*12500000000000000000^1024 ≤ 1723885591081861^1024*100000^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11373 100000 1723885591081861 12500000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11373/100000 : ℝ)) (X := (1723885591081861/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2821/20000 : ℝ) ^ (4187/1024 : ℝ) ≤ (4157282660557727/12500000000000000000 : ℝ) := by
    have hpowers : (2821/20000 : ℝ)^4187 ≤ (4157282660557727/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2821 : ℕ)^4187*12500000000000000000^1024 ≤ 4157282660557727^1024*20000^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2821 20000 4157282660557727 12500000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2821/20000 : ℝ)) (X := (4157282660557727/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251723885591081861/6250000000000000000 : ℝ) ≤ (10000674497240379/10000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (6251723885591081861/6250000000000000000 : ℝ)^1024 ≤ (10000674497240379/10000000000000000 : ℝ)^4187 := by
      have hnat : (6251723885591081861 : ℕ)^1024*10000000000000000^4187 ≤ 10000674497240379^4187*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251723885591081861 6250000000000000000 10000674497240379 10000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000674497240379/10000000000000000 : ℝ)) (X := (6251723885591081861/6250000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126470292062909897/3125000000000000000 : ℝ) ≤ (78133988008029/78125000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (3126470292062909897/3125000000000000000 : ℝ)^1024 ≤ (78133988008029/78125000000000 : ℝ)^4187 := by
      have hnat : (3126470292062909897 : ℕ)^1024*78125000000000^4187 ≤ 78133988008029^4187*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126470292062909897 3125000000000000000 78133988008029 78125000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78133988008029/78125000000000 : ℝ)) (X := (3126470292062909897/3125000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254157282660557727/6250000000000000000 : ℝ) ≤ (2000325286563009/2000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (6254157282660557727/6250000000000000000 : ℝ)^1024 ≤ (2000325286563009/2000000000000000 : ℝ)^4187 := by
      have hnat : (6254157282660557727 : ℕ)^1024*2000000000000000^4187 ≤ 2000325286563009^4187*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254157282660557727 6250000000000000000 2000325286563009 2000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000325286563009/2000000000000000 : ℝ)) (X := (6254157282660557727/6250000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1723885591081861/12500000000000000000 : ℝ) ≤ ((2731101636317003901/2732000000000000000 : ℝ)+2*(475967787333/273200000000000 : ℝ)*(11373/100000 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (2731101636317003901/2732000000000000000 : ℝ)+2*(475967787333/273200000000000 : ℝ)*(11373/100000 : ℝ)=(10000674497240379/10000000000000000 : ℝ) by norm_num, show 1+2*(1723885591081861/12500000000000000000 : ℝ)=(6251723885591081861/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4157282660557727/12500000000000000000 : ℝ)+(1723885591081861/12500000000000000000 : ℝ) ≤ ((2731101636317003901/2732000000000000000 : ℝ)+(475967787333/273200000000000 : ℝ)*((2821/20000 : ℝ)+(11373/100000 : ℝ)))^(4187/1024 : ℝ) := by
    rw [show (2731101636317003901/2732000000000000000 : ℝ)+(475967787333/273200000000000 : ℝ)*((2821/20000 : ℝ)+(11373/100000 : ℝ))=(78133988008029/78125000000000 : ℝ) by norm_num, show 1+(4157282660557727/12500000000000000000 : ℝ)+(1723885591081861/12500000000000000000 : ℝ)=(3126470292062909897/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4157282660557727/12500000000000000000 : ℝ) ≤ ((2731101636317003901/2732000000000000000 : ℝ)+2*(475967787333/273200000000000 : ℝ)*(2821/20000 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (2731101636317003901/2732000000000000000 : ℝ)+2*(475967787333/273200000000000 : ℝ)*(2821/20000 : ℝ)=(2000325286563009/2000000000000000 : ℝ) by norm_num, show 1+2*(4157282660557727/12500000000000000000 : ℝ)=(6254157282660557727/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2731101636317003901/2732000000000000000 : ℝ)*(X 1 0+X 2 0)+(475967787333/273200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (2731101636317003901/2732000000000000000 : ℝ)) (alpha := (475967787333/273200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2731101636317003901/2732000000000000000 : ℝ)*(X 0 1+X 2 1)+(475967787333/273200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (2731101636317003901/2732000000000000000 : ℝ)) (alpha := (475967787333/273200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2731101636317003901/2732000000000000000 : ℝ)*(X 0 2+X 1 2)+(475967787333/273200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (2731101636317003901/2732000000000000000 : ℝ)) (alpha := (475967787333/273200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-429575651/2000000000 : ℝ)*X 0 0+(2696289933/5000000000 : ℝ)*X 0 1+(526610579/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344666823/10000000000 : ℝ)*X 1 0+(-6912569/31250000 : ℝ)*X 1 1+(1053221167/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068933383/2000000000 : ℝ)*X 2 0+(5266105679/10000000000 : ℝ)*X 2 1+(-442404433/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179527501/5000000000 : ℝ)*X 0 0+(529259533/1250000000 : ℝ)*X 0 1+(28047933/62500000 : ℝ)*X 0 2+(2179527501/5000000000 : ℝ)*X 1 0+(529259533/1250000000 : ℝ)*X 1 1+(28047933/62500000 : ℝ)*X 1 2+(2179527501/5000000000 : ℝ)*X 2 0+(529259533/1250000000 : ℝ)*X 2 1+(28047933/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2147883169/10000000000 : ℝ)*X 0 0+(21065701/40000000 : ℝ)*X 0 1+(5392259197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312530723/10000000000 : ℝ)*X 1 0+(-521467157/2500000000 : ℝ)*X 1 1+(5392259193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312530719/10000000000 : ℝ)*X 2 0+(1348064799/2500000000 : ℝ)*X 2 1+(-2085868629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089766141/2500000000 : ℝ)*X 0 0+(4487028531/10000000000 : ℝ)*X 0 1+(4234719509/10000000000 : ℝ)*X 0 2+(1089766141/2500000000 : ℝ)*X 1 0+(4487028531/10000000000 : ℝ)*X 1 1+(4234719509/10000000000 : ℝ)*X 1 2+(1089766141/2500000000 : ℝ)*X 2 0+(4487028531/10000000000 : ℝ)*X 2 1+(4234719509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (339291520637397361395079941/68300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (195994743/25000000000000 : ℝ)*(base19) + (774350347/100000000000000 : ℝ)*(base23) + (114910033/100000000000000 : ℝ)*(lower2) + (219318277/100000000000000 : ℝ)*(upper3) + (1851067/5000000000000 : ℝ)*(lower4) + (2962536943346653/50000000000000 : ℝ)*(major0) + (2962536943346653/50000000000000 : ℝ)*(major1) + (2962536943346653/50000000000000 : ℝ)*(major2) + (3953390350498073/50000000000000 : ℝ)*(sp0) + (1581358954225291/20000000000000 : ℝ)*(sp1) + (7906794780755079/100000000000000 : ℝ)*(sp2) + (394333616029041/10000000000000 : ℝ)*(sp3) + (14854109281/100000000000000 : ℝ)*(sp4) + (1589240193/10000000000000 : ℝ)*(sp7) + (197167602634617/5000000000000 : ℝ)*(f.failure) + (7906795555105427/100000000000000 : ℝ)*(f.sum) + (28543264754981/6830000000000000000000000000 : ℝ)*base66 + (1072056881208816647/136600000000000000000000000000000 : ℝ)*base68 + (890773774628583353/136600000000000000000000000000000 : ℝ)*base69 + (320333275897783353/136600000000000000000000000000000 : ℝ)*base71 + (12350512990349/6830000000000000000000000000 : ℝ)*base73 + (1467594111716216647/136600000000000000000000000000000 : ℝ)*base76 + (3452105631085783353/136600000000000000000000000000000 : ℝ)*base77 + (1024882621738183353/136600000000000000000000000000000 : ℝ)*base79 + (5067243694399/6830000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3415399/500000000000000000000 : ℝ)*base90 + (3415399/500000000000000000000 : ℝ)*base92 + (3415399/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (250951500064493825606432727/34150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1335078041/100000000000000 : ℝ)*(base19) + (1447233417/100000000000000 : ℝ)*(base23) + (18365093/12500000000000 : ℝ)*(upper3) + (13552839/25000000000000 : ℝ)*(lower4) + (3771049/2500000000000 : ℝ)*(upper5) + (1488796649465809/25000000000000 : ℝ)*(major0) + (1488796649465809/25000000000000 : ℝ)*(major1) + (1488796649465809/25000000000000 : ℝ)*(major2) + (3686543317/10000000000000 : ℝ)*(sp1) + (39525974857/100000000000000 : ℝ)*(sp2) + (7946979794179569/100000000000000 : ℝ)*(sp4) + (7946941593668359/100000000000000 : ℝ)*(sp5) + (1589387764194259/20000000000000 : ℝ)*(sp6) + (1981696578298337/50000000000000 : ℝ)*(sp7) + (1981696578298337/50000000000000 : ℝ)*(f.failure) + (7946979794179569/100000000000000 : ℝ)*(f.sum) + (5630317201807/853750000000000000000000000 : ℝ)*base66 + (364734382257890909/68300000000000000000000000000000 : ℝ)*base67 + (150310902433390909/68300000000000000000000000000000 : ℝ)*base69 + (1018712815791809091/68300000000000000000000000000000 : ℝ)*base72 + (15849381371967/3415000000000000000000000000 : ℝ)*base73 + (1744384039901809091/68300000000000000000000000000000 : ℝ)*base76 + (250423518153709091/68300000000000000000000000000000 : ℝ)*base78 + (342783574248009091/68300000000000000000000000000000 : ℝ)*base80 + (5141367809593/3415000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (13754239/5000000000000000000000 : ℝ)*base90 + (13754239/5000000000000000000000 : ℝ)*base92 + (13754239/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1182_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1182_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1182_s7_0 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2147900163/10000000000 : ℝ)*x 0 + (33701991/62500000 : ℝ)*x 1 + (65829409/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147900163/10000000000 : ℝ)^8375 ≤ (3263866067263/25000000000000 : ℝ)^6327 := by
    have hnat : (2147900163 : ℕ)^8375*25000000000000^6327 ≤ 3263866067263^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147900163 10000000000 3263866067263 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33701991/62500000 : ℝ)^8375 ≤ (8830461362929/20000000000000 : ℝ)^6327 := by
    have hnat : (33701991 : ℕ)^8375*20000000000000^6327 ≤ 8830461362929^6327*62500000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33701991 62500000 8830461362929 20000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65829409/125000000 : ℝ)^8375 ≤ (42792228912449/100000000000000 : ℝ)^6327 := by
    have hnat : (65829409 : ℕ)^8375*100000000000000^6327 ≤ 42792228912449^6327*125000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65829409 125000000 42792228912449 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2147900163/10000000000 : ℝ), (33701991/62500000 : ℝ), (65829409/125000000 : ℝ)] ![(3263866067263/25000000000000 : ℝ), (8830461362929/20000000000000 : ℝ), (42792228912449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2147900163/10000000000 : ℝ)|^8375 ≤ (3263866067263/25000000000000 : ℝ)^6327
        have hw : |(-2147900163/10000000000 : ℝ)|=(2147900163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33701991/62500000 : ℝ)|^8375 ≤ (8830461362929/20000000000000 : ℝ)^6327
        have hw : |(33701991/62500000 : ℝ)|=(33701991/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65829409/125000000 : ℝ)|^8375 ≤ (42792228912449/100000000000000 : ℝ)^6327
        have hw : |(65829409/125000000 : ℝ)|=(65829409/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s7_1 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534460117/1000000000 : ℝ)*x 0 + (-1105891257/5000000000 : ℝ)*x 1 + (65829409/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534460117/1000000000 : ℝ)^8375 ≤ (10908967310477/25000000000000 : ℝ)^6327 := by
    have hnat : (534460117 : ℕ)^8375*25000000000000^6327 ≤ 10908967310477^6327*1000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534460117 1000000000 10908967310477 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105891257/5000000000 : ℝ)^8375 ≤ (13571901831139/100000000000000 : ℝ)^6327 := by
    have hnat : (1105891257 : ℕ)^8375*100000000000000^6327 ≤ 13571901831139^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105891257 5000000000 13571901831139 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65829409/125000000 : ℝ)^8375 ≤ (42792228912449/100000000000000 : ℝ)^6327 := by
    have hnat : (65829409 : ℕ)^8375*100000000000000^6327 ≤ 42792228912449^6327*125000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65829409 125000000 42792228912449 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534460117/1000000000 : ℝ), (-1105891257/5000000000 : ℝ), (65829409/125000000 : ℝ)] ![(10908967310477/25000000000000 : ℝ), (13571901831139/100000000000000 : ℝ), (42792228912449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534460117/1000000000 : ℝ)|^8375 ≤ (10908967310477/25000000000000 : ℝ)^6327
        have hw : |(534460117/1000000000 : ℝ)|=(534460117/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1105891257/5000000000 : ℝ)|^8375 ≤ (13571901831139/100000000000000 : ℝ)^6327
        have hw : |(-1105891257/5000000000 : ℝ)|=(1105891257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65829409/125000000 : ℝ)|^8375 ≤ (42792228912449/100000000000000 : ℝ)^6327
        have hw : |(65829409/125000000 : ℝ)|=(65829409/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s7_2 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334037573/625000000 : ℝ)*x 0 + (2633176361/5000000000 : ℝ)*x 1 + (-1105891257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334037573/625000000 : ℝ)^8375 ≤ (21817934610147/50000000000000 : ℝ)^6327 := by
    have hnat : (334037573 : ℕ)^8375*50000000000000^6327 ≤ 21817934610147^6327*625000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334037573 625000000 21817934610147 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633176361/5000000000 : ℝ)^8375 ≤ (1069805723349/2500000000000 : ℝ)^6327 := by
    have hnat : (2633176361 : ℕ)^8375*2500000000000^6327 ≤ 1069805723349^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633176361 5000000000 1069805723349 2500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105891257/5000000000 : ℝ)^8375 ≤ (13571901831139/100000000000000 : ℝ)^6327 := by
    have hnat : (1105891257 : ℕ)^8375*100000000000000^6327 ≤ 13571901831139^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105891257 5000000000 13571901831139 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334037573/625000000 : ℝ), (2633176361/5000000000 : ℝ), (-1105891257/5000000000 : ℝ)] ![(21817934610147/50000000000000 : ℝ), (1069805723349/2500000000000 : ℝ), (13571901831139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334037573/625000000 : ℝ)|^8375 ≤ (21817934610147/50000000000000 : ℝ)^6327
        have hw : |(334037573/625000000 : ℝ)|=(334037573/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633176361/5000000000 : ℝ)|^8375 ≤ (1069805723349/2500000000000 : ℝ)^6327
        have hw : |(2633176361/5000000000 : ℝ)|=(2633176361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1105891257/5000000000 : ℝ)|^8375 ≤ (13571901831139/100000000000000 : ℝ)^6327
        have hw : |(-1105891257/5000000000 : ℝ)|=(1105891257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s7_3 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179533871/5000000000 : ℝ)*x 0 + (1058646113/2500000000 : ℝ)*x 1 + (4487157931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179533871/5000000000 : ℝ)^8375 ≤ (4164646937189/12500000000000 : ℝ)^6327 := by
    have hnat : (2179533871 : ℕ)^8375*12500000000000^6327 ≤ 4164646937189^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179533871 5000000000 4164646937189 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058646113/2500000000 : ℝ)^8375 ≤ (1282544340829/4000000000000 : ℝ)^6327 := by
    have hnat : (1058646113 : ℕ)^8375*4000000000000^6327 ≤ 1282544340829^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058646113 2500000000 1282544340829 4000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487157931/10000000000 : ℝ)^8375 ≤ (8654803988799/25000000000000 : ℝ)^6327 := by
    have hnat : (4487157931 : ℕ)^8375*25000000000000^6327 ≤ 8654803988799^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487157931 10000000000 8654803988799 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179533871/5000000000 : ℝ), (1058646113/2500000000 : ℝ), (4487157931/10000000000 : ℝ)] ![(4164646937189/12500000000000 : ℝ), (1282544340829/4000000000000 : ℝ), (8654803988799/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179533871/5000000000 : ℝ)|^8375 ≤ (4164646937189/12500000000000 : ℝ)^6327
        have hw : |(2179533871/5000000000 : ℝ)|=(2179533871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1058646113/2500000000 : ℝ)|^8375 ≤ (1282544340829/4000000000000 : ℝ)^6327
        have hw : |(1058646113/2500000000 : ℝ)|=(1058646113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487157931/10000000000 : ℝ)|^8375 ≤ (8654803988799/25000000000000 : ℝ)^6327
        have hw : |(4487157931/10000000000 : ℝ)|=(4487157931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s7_4 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1073952481/5000000000 : ℝ)*x 0 + (2633334841/5000000000 : ℝ)*x 1 + (1348000111/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073952481/5000000000 : ℝ)^8375 ≤ (13055502880503/100000000000000 : ℝ)^6327 := by
    have hnat : (1073952481 : ℕ)^8375*100000000000000^6327 ≤ 13055502880503^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073952481 5000000000 13055502880503 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633334841/5000000000 : ℝ)^8375 ≤ (42795638119477/100000000000000 : ℝ)^6327 := by
    have hnat : (2633334841 : ℕ)^8375*100000000000000^6327 ≤ 42795638119477^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633334841 5000000000 42795638119477 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348000111/2500000000 : ℝ)^8375 ≤ (2759303686361/6250000000000 : ℝ)^6327 := by
    have hnat : (1348000111 : ℕ)^8375*6250000000000^6327 ≤ 2759303686361^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348000111 2500000000 2759303686361 6250000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1073952481/5000000000 : ℝ), (2633334841/5000000000 : ℝ), (1348000111/2500000000 : ℝ)] ![(13055502880503/100000000000000 : ℝ), (42795638119477/100000000000000 : ℝ), (2759303686361/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1073952481/5000000000 : ℝ)|^8375 ≤ (13055502880503/100000000000000 : ℝ)^6327
        have hw : |(-1073952481/5000000000 : ℝ)|=(1073952481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633334841/5000000000 : ℝ)|^8375 ≤ (42795638119477/100000000000000 : ℝ)^6327
        have hw : |(2633334841/5000000000 : ℝ)|=(2633334841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348000111/2500000000 : ℝ)|^8375 ≤ (2759303686361/6250000000000 : ℝ)^6327
        have hw : |(1348000111/2500000000 : ℝ)|=(1348000111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s7_5 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062518809/2000000000 : ℝ)*x 0 + (-65191713/312500000 : ℝ)*x 1 + (2696000217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062518809/2000000000 : ℝ)^8375 ≤ (21645147937479/50000000000000 : ℝ)^6327 := by
    have hnat : (1062518809 : ℕ)^8375*50000000000000^6327 ≤ 21645147937479^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062518809 2000000000 21645147937479 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65191713/312500000 : ℝ)^8375 ≤ (157010565569/1250000000000 : ℝ)^6327 := by
    have hnat : (65191713 : ℕ)^8375*1250000000000^6327 ≤ 157010565569^6327*312500000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65191713 312500000 157010565569 1250000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696000217/5000000000 : ℝ)^8375 ≤ (22074429436697/50000000000000 : ℝ)^6327 := by
    have hnat : (2696000217 : ℕ)^8375*50000000000000^6327 ≤ 22074429436697^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696000217 5000000000 22074429436697 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062518809/2000000000 : ℝ), (-65191713/312500000 : ℝ), (2696000217/5000000000 : ℝ)] ![(21645147937479/50000000000000 : ℝ), (157010565569/1250000000000 : ℝ), (22074429436697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062518809/2000000000 : ℝ)|^8375 ≤ (21645147937479/50000000000000 : ℝ)^6327
        have hw : |(1062518809/2000000000 : ℝ)|=(1062518809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-65191713/312500000 : ℝ)|^8375 ≤ (157010565569/1250000000000 : ℝ)^6327
        have hw : |(-65191713/312500000 : ℝ)|=(65191713/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696000217/5000000000 : ℝ)|^8375 ≤ (22074429436697/50000000000000 : ℝ)^6327
        have hw : |(2696000217/5000000000 : ℝ)|=(2696000217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s7_6 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062518809/2000000000 : ℝ)*x 0 + (1348000109/2500000000 : ℝ)*x 1 + (-521533703/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062518809/2000000000 : ℝ)^8375 ≤ (21645147937479/50000000000000 : ℝ)^6327 := by
    have hnat : (1062518809 : ℕ)^8375*50000000000000^6327 ≤ 21645147937479^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062518809 2000000000 21645147937479 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348000109/2500000000 : ℝ)^8375 ≤ (4414885889507/10000000000000 : ℝ)^6327 := by
    have hnat : (1348000109 : ℕ)^8375*10000000000000^6327 ≤ 4414885889507^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348000109 2500000000 4414885889507 10000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521533703/2500000000 : ℝ)^8375 ≤ (12560845213639/100000000000000 : ℝ)^6327 := by
    have hnat : (521533703 : ℕ)^8375*100000000000000^6327 ≤ 12560845213639^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521533703 2500000000 12560845213639 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062518809/2000000000 : ℝ), (1348000109/2500000000 : ℝ), (-521533703/2500000000 : ℝ)] ![(21645147937479/50000000000000 : ℝ), (4414885889507/10000000000000 : ℝ), (12560845213639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062518809/2000000000 : ℝ)|^8375 ≤ (21645147937479/50000000000000 : ℝ)^6327
        have hw : |(1062518809/2000000000 : ℝ)|=(1062518809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348000109/2500000000 : ℝ)|^8375 ≤ (4414885889507/10000000000000 : ℝ)^6327
        have hw : |(1348000109/2500000000 : ℝ)|=(1348000109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-521533703/2500000000 : ℝ)|^8375 ≤ (12560845213639/100000000000000 : ℝ)^6327
        have hw : |(-521533703/2500000000 : ℝ)|=(521533703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s7_7 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179538693/5000000000 : ℝ)*x 0 + (224326113/500000000 : ℝ)*x 1 + (529402799/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179538693/5000000000 : ℝ)^8375 ≤ (16658636534047/50000000000000 : ℝ)^6327 := by
    have hnat : (2179538693 : ℕ)^8375*50000000000000^6327 ≤ 16658636534047^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179538693 5000000000 16658636534047 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224326113/500000000 : ℝ)^8375 ≤ (34612724302233/100000000000000 : ℝ)^6327 := by
    have hnat : (224326113 : ℕ)^8375*100000000000000^6327 ≤ 34612724302233^6327*500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224326113 500000000 34612724302233 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529402799/1250000000 : ℝ)^8375 ≤ (801750065363/2500000000000 : ℝ)^6327 := by
    have hnat : (529402799 : ℕ)^8375*2500000000000^6327 ≤ 801750065363^6327*1250000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529402799 1250000000 801750065363 2500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179538693/5000000000 : ℝ), (224326113/500000000 : ℝ), (529402799/1250000000 : ℝ)] ![(16658636534047/50000000000000 : ℝ), (34612724302233/100000000000000 : ℝ), (801750065363/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179538693/5000000000 : ℝ)|^8375 ≤ (16658636534047/50000000000000 : ℝ)^6327
        have hw : |(2179538693/5000000000 : ℝ)|=(2179538693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224326113/500000000 : ℝ)|^8375 ≤ (34612724302233/100000000000000 : ℝ)^6327
        have hw : |(224326113/500000000 : ℝ)|=(224326113/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529402799/1250000000 : ℝ)|^8375 ≤ (801750065363/2500000000000 : ℝ)^6327
        have hw : |(529402799/1250000000 : ℝ)|=(529402799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1182_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2851/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1759/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7039/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7039/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7039/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7039/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7039/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7039/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11399/100000 : ℝ) ^ (4187/1024 : ℝ) ≤ (13920454514771411/100000000000000000000 : ℝ) := by
    have hpowers : (11399/100000 : ℝ)^4187 ≤ (13920454514771411/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11399 : ℕ)^4187*100000000000000000000^1024 ≤ 13920454514771411^1024*100000^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11399 100000 13920454514771411 100000000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11399/100000 : ℝ)) (X := (13920454514771411/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7039/50000 : ℝ) ^ (4187/1024 : ℝ) ≤ (32998718419587967/100000000000000000000 : ℝ) := by
    have hpowers : (7039/50000 : ℝ)^4187 ≤ (32998718419587967/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7039 : ℕ)^4187*100000000000000000000^1024 ≤ 32998718419587967^1024*50000^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7039 50000 32998718419587967 100000000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7039/50000 : ℝ)) (X := (32998718419587967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013920454514771411/50000000000000000000 : ℝ) ≤ (10000680823819561/10000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (50013920454514771411/50000000000000000000 : ℝ)^1024 ≤ (10000680823819561/10000000000000000 : ℝ)^4187 := by
      have hnat : (50013920454514771411 : ℕ)^1024*10000000000000000^4187 ≤ 10000680823819561^4187*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013920454514771411 50000000000000000000 10000680823819561 10000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000680823819561/10000000000000000 : ℝ)) (X := (50013920454514771411/50000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023459586467179689/50000000000000000000 : ℝ) ≤ (10001147282559589/10000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (50023459586467179689/50000000000000000000 : ℝ)^1024 ≤ (10001147282559589/10000000000000000 : ℝ)^4187 := by
      have hnat : (50023459586467179689 : ℕ)^1024*10000000000000000^4187 ≤ 10001147282559589^4187*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023459586467179689 50000000000000000000 10001147282559589 10000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001147282559589/10000000000000000 : ℝ)) (X := (50023459586467179689/50000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032998718419587967/50000000000000000000 : ℝ) ≤ (10001613741299617/10000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (50032998718419587967/50000000000000000000 : ℝ)^1024 ≤ (10001613741299617/10000000000000000 : ℝ)^4187 := by
      have hnat : (50032998718419587967 : ℕ)^1024*10000000000000000^4187 ≤ 10001613741299617^4187*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032998718419587967 50000000000000000000 10001613741299617 10000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001613741299617/10000000000000000 : ℝ)) (X := (50032998718419587967/50000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13920454514771411/100000000000000000000 : ℝ) ≤ ((357082528008765941/357200000000000000 : ℝ)+2*(38871561669/22325000000000 : ℝ)*(11399/100000 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (357082528008765941/357200000000000000 : ℝ)+2*(38871561669/22325000000000 : ℝ)*(11399/100000 : ℝ)=(10000680823819561/10000000000000000 : ℝ) by norm_num, show 1+2*(13920454514771411/100000000000000000000 : ℝ)=(50013920454514771411/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32998718419587967/100000000000000000000 : ℝ)+(13920454514771411/100000000000000000000 : ℝ) ≤ ((357082528008765941/357200000000000000 : ℝ)+(38871561669/22325000000000 : ℝ)*((7039/50000 : ℝ)+(11399/100000 : ℝ)))^(4187/1024 : ℝ) := by
    rw [show (357082528008765941/357200000000000000 : ℝ)+(38871561669/22325000000000 : ℝ)*((7039/50000 : ℝ)+(11399/100000 : ℝ))=(10001147282559589/10000000000000000 : ℝ) by norm_num, show 1+(32998718419587967/100000000000000000000 : ℝ)+(13920454514771411/100000000000000000000 : ℝ)=(50023459586467179689/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32998718419587967/100000000000000000000 : ℝ) ≤ ((357082528008765941/357200000000000000 : ℝ)+2*(38871561669/22325000000000 : ℝ)*(7039/50000 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (357082528008765941/357200000000000000 : ℝ)+2*(38871561669/22325000000000 : ℝ)*(7039/50000 : ℝ)=(10001613741299617/10000000000000000 : ℝ) by norm_num, show 1+2*(32998718419587967/100000000000000000000 : ℝ)=(50032998718419587967/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (357082528008765941/357200000000000000 : ℝ)*(X 1 0+X 2 0)+(38871561669/22325000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (357082528008765941/357200000000000000 : ℝ)) (alpha := (38871561669/22325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (357082528008765941/357200000000000000 : ℝ)*(X 0 1+X 2 1)+(38871561669/22325000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (357082528008765941/357200000000000000 : ℝ)) (alpha := (38871561669/22325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (357082528008765941/357200000000000000 : ℝ)*(X 0 2+X 1 2)+(38871561669/22325000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (357082528008765941/357200000000000000 : ℝ)) (alpha := (38871561669/22325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2147900163/10000000000 : ℝ)*X 0 0+(33701991/62500000 : ℝ)*X 0 1+(65829409/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534460117/1000000000 : ℝ)*X 1 0+(-1105891257/5000000000 : ℝ)*X 1 1+(65829409/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334037573/625000000 : ℝ)*X 2 0+(2633176361/5000000000 : ℝ)*X 2 1+(-1105891257/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179533871/5000000000 : ℝ)*X 0 0+(1058646113/2500000000 : ℝ)*X 0 1+(4487157931/10000000000 : ℝ)*X 0 2+(2179533871/5000000000 : ℝ)*X 1 0+(1058646113/2500000000 : ℝ)*X 1 1+(4487157931/10000000000 : ℝ)*X 1 2+(2179533871/5000000000 : ℝ)*X 2 0+(1058646113/2500000000 : ℝ)*X 2 1+(4487157931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1073952481/5000000000 : ℝ)*X 0 0+(2633334841/5000000000 : ℝ)*X 0 1+(1348000111/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062518809/2000000000 : ℝ)*X 1 0+(-65191713/312500000 : ℝ)*X 1 1+(2696000217/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062518809/2000000000 : ℝ)*X 2 0+(1348000109/2500000000 : ℝ)*X 2 1+(-521533703/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2179538693/5000000000 : ℝ)*X 0 0+(224326113/500000000 : ℝ)*X 0 1+(529402799/1250000000 : ℝ)*X 0 2+(2179538693/5000000000 : ℝ)*X 1 0+(224326113/500000000 : ℝ)*X 1 1+(529402799/1250000000 : ℝ)*X 1 2+(2179538693/5000000000 : ℝ)*X 2 0+(224326113/500000000 : ℝ)*X 2 1+(529402799/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1981348398200822416645881/279062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (694726999/50000000000000 : ℝ)*(base19) + (161329033/12500000000000 : ℝ)*(base23) + (3201783/6250000000000 : ℝ)*(lower2) + (7136107/4000000000000 : ℝ)*(upper3) + (107165209/100000000000000 : ℝ)*(upper5) + (46476646531863/781250000000 : ℝ)*(major0) + (46476646531863/781250000000 : ℝ)*(major1) + (46476646531863/781250000000 : ℝ)*(major2) + (248084381828229/3125000000000 : ℝ)*(sp0) + (15877473953287/200000000000 : ℝ)*(sp1) + (3969368537732617/50000000000000 : ℝ)*(sp2) + (1979631181704909/50000000000000 : ℝ)*(sp3) + (38147594169/100000000000000 : ℝ)*(sp4) + (10272991191/50000000000000 : ℝ)*(sp7) + (19796414546961/500000000000 : ℝ)*(f.failure) + (3969369183048749/50000000000000 : ℝ)*(f.sum) + (6929278811763/2232500000000000000000000000 : ℝ)*base66 + (504505707670979/139531250000000000000000000000 : ℝ)*base67 + (3924569780159729/139531250000000000000000000000 : ℝ)*base69 + (633679492935083/279062500000000000000000000000 : ℝ)*base71 + (1510320303203/558125000000000000000000000 : ℝ)*base73 + (626256682306651/34882812500000000000000000000 : ℝ)*base75 + (352691932742583/279062500000000000000000000000 : ℝ)*base77 + (343778039113833/279062500000000000000000000000 : ℝ)*base79 + (14427149589787/2232500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (44367/50000000000000000000 : ℝ)*base90 + (44367/50000000000000000000 : ℝ)*base92 + (44367/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1721395908622290387616407/714400000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216880339/50000000000000 : ℝ)*(base19) + (47349007/10000000000000 : ℝ)*(base23) + (17963017/100000000000000 : ℝ)*(upper3) + (5244387/20000000000000 : ℝ)*(lower4) + (97750789/100000000000000 : ℝ)*(upper5) + (239163962531191/4000000000000 : ℝ)*(major0) + (239163962531191/4000000000000 : ℝ)*(major1) + (239163962531191/4000000000000 : ℝ)*(major2) + (6921534403/50000000000000 : ℝ)*(sp1) + (12244887173/100000000000000 : ℝ)*(sp2) + (7978890274672271/100000000000000 : ℝ)*(sp4) + (3989437998921393/50000000000000 : ℝ)*(sp5) + (1994719389073757/25000000000000 : ℝ)*(sp6) + (1989653885784157/50000000000000 : ℝ)*(sp7) + (1989653885784157/50000000000000 : ℝ)*(f.failure) + (7978890274672271/100000000000000 : ℝ)*(f.sum) + (318878213353/446500000000000000000000000 : ℝ)*base66 + (6765417773724131/1428800000000000000000000000000 : ℝ)*base67 + (10163601793235869/1428800000000000000000000000000 : ℝ)*base70 + (2052375047522531/1428800000000000000000000000000 : ℝ)*base71 + (32367807393/11162500000000000000000000 : ℝ)*base73 + (7532753284908131/1428800000000000000000000000000 : ℝ)*base75 + (1806601538623331/1428800000000000000000000000000 : ℝ)*base77 + (3908117278685469/1428800000000000000000000000000 : ℝ)*base80 + (430445097541/89300000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (28651779/5000000000000000000000 : ℝ)*base90 + (28651779/5000000000000000000000 : ℝ)*base92 + (28651779/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1182_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1182_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1182_s8_0 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-134244199/625000000 : ℝ)*x 0 + (107845273/200000000 : ℝ)*x 1 + (5266402799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134244199/625000000 : ℝ)^8375 ≤ (13055520758121/100000000000000 : ℝ)^6327 := by
    have hnat : (134244199 : ℕ)^8375*100000000000000^6327 ≤ 13055520758121^6327*625000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134244199 625000000 13055520758121 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107845273/200000000 : ℝ)^8375 ≤ (44151711679541/100000000000000 : ℝ)^6327 := by
    have hnat : (107845273 : ℕ)^8375*100000000000000^6327 ≤ 44151711679541^6327*200000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107845273 200000000 44151711679541 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266402799/10000000000 : ℝ)^8375 ≤ (42792767552029/100000000000000 : ℝ)^6327 := by
    have hnat : (5266402799 : ℕ)^8375*100000000000000^6327 ≤ 42792767552029^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266402799 10000000000 42792767552029 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-134244199/625000000 : ℝ), (107845273/200000000 : ℝ), (5266402799/10000000000 : ℝ)] ![(13055520758121/100000000000000 : ℝ), (44151711679541/100000000000000 : ℝ), (42792767552029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-134244199/625000000 : ℝ)|^8375 ≤ (13055520758121/100000000000000 : ℝ)^6327
        have hw : |(-134244199/625000000 : ℝ)|=(134244199/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107845273/200000000 : ℝ)|^8375 ≤ (44151711679541/100000000000000 : ℝ)^6327
        have hw : |(107845273/200000000 : ℝ)|=(107845273/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266402799/10000000000 : ℝ)|^8375 ≤ (42792767552029/100000000000000 : ℝ)^6327
        have hw : |(5266402799/10000000000 : ℝ)|=(5266402799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s8_1 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672293303/5000000000 : ℝ)*x 0 + (-34558367/156250000 : ℝ)*x 1 + (1053280573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672293303/5000000000 : ℝ)^8375 ≤ (10908927961287/25000000000000 : ℝ)^6327 := by
    have hnat : (2672293303 : ℕ)^8375*25000000000000^6327 ≤ 10908927961287^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672293303 5000000000 10908927961287 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34558367/156250000 : ℝ)^8375 ≤ (13571519867681/100000000000000 : ℝ)^6327 := by
    have hnat : (34558367 : ℕ)^8375*100000000000000^6327 ≤ 13571519867681^6327*156250000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34558367 156250000 13571519867681 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053280573/2000000000 : ℝ)^8375 ≤ (5349096032739/12500000000000 : ℝ)^6327 := by
    have hnat : (1053280573 : ℕ)^8375*12500000000000^6327 ≤ 5349096032739^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053280573 2000000000 5349096032739 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672293303/5000000000 : ℝ), (-34558367/156250000 : ℝ), (1053280573/2000000000 : ℝ)] ![(10908927961287/25000000000000 : ℝ), (13571519867681/100000000000000 : ℝ), (5349096032739/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672293303/5000000000 : ℝ)|^8375 ≤ (10908927961287/25000000000000 : ℝ)^6327
        have hw : |(2672293303/5000000000 : ℝ)|=(2672293303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34558367/156250000 : ℝ)|^8375 ≤ (13571519867681/100000000000000 : ℝ)^6327
        have hw : |(-34558367/156250000 : ℝ)|=(34558367/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053280573/2000000000 : ℝ)|^8375 ≤ (5349096032739/12500000000000 : ℝ)^6327
        have hw : |(1053280573/2000000000 : ℝ)|=(1053280573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s8_2 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344586607/10000000000 : ℝ)*x 0 + (5266402847/10000000000 : ℝ)*x 1 + (-2211735513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344586607/10000000000 : ℝ)^8375 ≤ (8727142371191/20000000000000 : ℝ)^6327 := by
    have hnat : (5344586607 : ℕ)^8375*20000000000000^6327 ≤ 8727142371191^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344586607 10000000000 8727142371191 20000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266402847/10000000000 : ℝ)^8375 ≤ (10698192017077/25000000000000 : ℝ)^6327 := by
    have hnat : (5266402847 : ℕ)^8375*25000000000000^6327 ≤ 10698192017077^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266402847 10000000000 10698192017077 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2211735513/10000000000 : ℝ)^8375 ≤ (678576003537/5000000000000 : ℝ)^6327 := by
    have hnat : (2211735513 : ℕ)^8375*5000000000000^6327 ≤ 678576003537^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211735513 10000000000 678576003537 5000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344586607/10000000000 : ℝ), (5266402847/10000000000 : ℝ), (-2211735513/10000000000 : ℝ)] ![(8727142371191/20000000000000 : ℝ), (10698192017077/25000000000000 : ℝ), (678576003537/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344586607/10000000000 : ℝ)|^8375 ≤ (8727142371191/20000000000000 : ℝ)^6327
        have hw : |(5344586607/10000000000 : ℝ)|=(5344586607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266402847/10000000000 : ℝ)|^8375 ≤ (10698192017077/25000000000000 : ℝ)^6327
        have hw : |(5266402847/10000000000 : ℝ)|=(5266402847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2211735513/10000000000 : ℝ)|^8375 ≤ (678576003537/5000000000000 : ℝ)^6327
        have hw : |(-2211735513/10000000000 : ℝ)|=(2211735513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s8_3 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089767613/2500000000 : ℝ)*x 0 + (4234689267/10000000000 : ℝ)*x 1 + (4487052379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089767613/2500000000 : ℝ)^8375 ≤ (16658601457601/50000000000000 : ℝ)^6327 := by
    have hnat : (1089767613 : ℕ)^8375*50000000000000^6327 ≤ 16658601457601^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089767613 2500000000 16658601457601 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4234689267/10000000000 : ℝ)^8375 ≤ (4008082382943/12500000000000 : ℝ)^6327 := by
    have hnat : (4234689267 : ℕ)^8375*12500000000000^6327 ≤ 4008082382943^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234689267 10000000000 4008082382943 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487052379/10000000000 : ℝ)^8375 ≤ (34618138007553/100000000000000 : ℝ)^6327 := by
    have hnat : (4487052379 : ℕ)^8375*100000000000000^6327 ≤ 34618138007553^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487052379 10000000000 34618138007553 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089767613/2500000000 : ℝ), (4234689267/10000000000 : ℝ), (4487052379/10000000000 : ℝ)] ![(16658601457601/50000000000000 : ℝ), (4008082382943/12500000000000 : ℝ), (34618138007553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089767613/2500000000 : ℝ)|^8375 ≤ (16658601457601/50000000000000 : ℝ)^6327
        have hw : |(1089767613/2500000000 : ℝ)|=(1089767613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4234689267/10000000000 : ℝ)|^8375 ≤ (4008082382943/12500000000000 : ℝ)^6327
        have hw : |(4234689267/10000000000 : ℝ)|=(4234689267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487052379/10000000000 : ℝ)|^8375 ≤ (34618138007553/100000000000000 : ℝ)^6327
        have hw : |(4487052379/10000000000 : ℝ)|=(4487052379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s8_4 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1073955991/5000000000 : ℝ)*x 0 + (5266719281/10000000000 : ℝ)*x 1 + (539194601/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073955991/5000000000 : ℝ)^8375 ≤ (6527779680783/50000000000000 : ℝ)^6327 := by
    have hnat : (1073955991 : ℕ)^8375*50000000000000^6327 ≤ 6527779680783^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073955991 5000000000 6527779680783 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266719281/10000000000 : ℝ)^8375 ≤ (2139808580333/5000000000000 : ℝ)^6327 := by
    have hnat : (5266719281 : ℕ)^8375*5000000000000^6327 ≤ 2139808580333^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266719281 10000000000 2139808580333 5000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539194601/1000000000 : ℝ)^8375 ≤ (11037067254249/25000000000000 : ℝ)^6327 := by
    have hnat : (539194601 : ℕ)^8375*25000000000000^6327 ≤ 11037067254249^6327*1000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539194601 1000000000 11037067254249 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1073955991/5000000000 : ℝ), (5266719281/10000000000 : ℝ), (539194601/1000000000 : ℝ)] ![(6527779680783/50000000000000 : ℝ), (2139808580333/5000000000000 : ℝ), (11037067254249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1073955991/5000000000 : ℝ)|^8375 ≤ (6527779680783/50000000000000 : ℝ)^6327
        have hw : |(-1073955991/5000000000 : ℝ)|=(1073955991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266719281/10000000000 : ℝ)|^8375 ≤ (2139808580333/5000000000000 : ℝ)^6327
        have hw : |(5266719281/10000000000 : ℝ)|=(5266719281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539194601/1000000000 : ℝ)|^8375 ≤ (11037067254249/25000000000000 : ℝ)^6327
        have hw : |(539194601/1000000000 : ℝ)|=(539194601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s8_5 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212504251/400000000 : ℝ)*x 0 + (-1043096139/5000000000 : ℝ)*x 1 + (1078389201/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212504251/400000000 : ℝ)^8375 ≤ (43290427790973/100000000000000 : ℝ)^6327 := by
    have hnat : (212504251 : ℕ)^8375*100000000000000^6327 ≤ 43290427790973^6327*400000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212504251 400000000 43290427790973 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043096139/5000000000 : ℝ)^8375 ≤ (785081451571/6250000000000 : ℝ)^6327 := by
    have hnat : (1043096139 : ℕ)^8375*6250000000000^6327 ≤ 785081451571^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043096139 5000000000 785081451571 6250000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078389201/2000000000 : ℝ)^8375 ≤ (22074134481403/50000000000000 : ℝ)^6327 := by
    have hnat : (1078389201 : ℕ)^8375*50000000000000^6327 ≤ 22074134481403^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078389201 2000000000 22074134481403 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212504251/400000000 : ℝ), (-1043096139/5000000000 : ℝ), (1078389201/2000000000 : ℝ)] ![(43290427790973/100000000000000 : ℝ), (785081451571/6250000000000 : ℝ), (22074134481403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212504251/400000000 : ℝ)|^8375 ≤ (43290427790973/100000000000000 : ℝ)^6327
        have hw : |(212504251/400000000 : ℝ)|=(212504251/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1043096139/5000000000 : ℝ)|^8375 ≤ (785081451571/6250000000000 : ℝ)^6327
        have hw : |(-1043096139/5000000000 : ℝ)|=(1043096139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078389201/2000000000 : ℝ)|^8375 ≤ (22074134481403/50000000000000 : ℝ)^6327
        have hw : |(1078389201/2000000000 : ℝ)|=(1078389201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s8_6 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531260627/1000000000 : ℝ)*x 0 + (2695973007/5000000000 : ℝ)*x 1 + (-83447691/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531260627/1000000000 : ℝ)^8375 ≤ (43290427737041/100000000000000 : ℝ)^6327 := by
    have hnat : (531260627 : ℕ)^8375*100000000000000^6327 ≤ 43290427737041^6327*1000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531260627 1000000000 43290427737041 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695973007/5000000000 : ℝ)^8375 ≤ (44148269060349/100000000000000 : ℝ)^6327 := by
    have hnat : (2695973007 : ℕ)^8375*100000000000000^6327 ≤ 44148269060349^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695973007 5000000000 44148269060349 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83447691/400000000 : ℝ)^8375 ≤ (502452128049/4000000000000 : ℝ)^6327 := by
    have hnat : (83447691 : ℕ)^8375*4000000000000^6327 ≤ 502452128049^6327*400000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83447691 400000000 502452128049 4000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531260627/1000000000 : ℝ), (2695973007/5000000000 : ℝ), (-83447691/400000000 : ℝ)] ![(43290427737041/100000000000000 : ℝ), (44148269060349/100000000000000 : ℝ), (502452128049/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531260627/1000000000 : ℝ)|^8375 ≤ (43290427737041/100000000000000 : ℝ)^6327
        have hw : |(531260627/1000000000 : ℝ)|=(531260627/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695973007/5000000000 : ℝ)|^8375 ≤ (44148269060349/100000000000000 : ℝ)^6327
        have hw : |(2695973007/5000000000 : ℝ)|=(2695973007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83447691/400000000 : ℝ)|^8375 ≤ (502452128049/4000000000000 : ℝ)^6327
        have hw : |(-83447691/400000000 : ℝ)|=(83447691/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s8_7 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089770001/2500000000 : ℝ)*x 0 + (280401109/625000000 : ℝ)*x 1 + (529415779/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089770001/2500000000 : ℝ)^8375 ≤ (16658649777509/50000000000000 : ℝ)^6327 := by
    have hnat : (1089770001 : ℕ)^8375*50000000000000^6327 ≤ 16658649777509^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089770001 2500000000 16658649777509 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280401109/625000000 : ℝ)^8375 ≤ (34611656983627/100000000000000 : ℝ)^6327 := by
    have hnat : (280401109 : ℕ)^8375*100000000000000^6327 ≤ 34611656983627^6327*625000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280401109 625000000 34611656983627 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529415779/1250000000 : ℝ)^8375 ≤ (32071043435791/100000000000000 : ℝ)^6327 := by
    have hnat : (529415779 : ℕ)^8375*100000000000000^6327 ≤ 32071043435791^6327*1250000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529415779 1250000000 32071043435791 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089770001/2500000000 : ℝ), (280401109/625000000 : ℝ), (529415779/1250000000 : ℝ)] ![(16658649777509/50000000000000 : ℝ), (34611656983627/100000000000000 : ℝ), (32071043435791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089770001/2500000000 : ℝ)|^8375 ≤ (16658649777509/50000000000000 : ℝ)^6327
        have hw : |(1089770001/2500000000 : ℝ)|=(1089770001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280401109/625000000 : ℝ)|^8375 ≤ (34611656983627/100000000000000 : ℝ)^6327
        have hw : |(280401109/625000000 : ℝ)|=(280401109/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529415779/1250000000 : ℝ)|^8375 ≤ (32071043435791/100000000000000 : ℝ)^6327
        have hw : |(529415779/1250000000 : ℝ)|=(529415779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1182_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2281/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14071/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1759/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2851/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1759/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2851/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1759/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2851/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1759/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2851/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1759/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2851/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1759/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2851/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2851/25000 : ℝ) ^ (4187/1024 : ℝ) ≤ (435794939023351/3125000000000000000 : ℝ) := by
    have hpowers : (2851/25000 : ℝ)^4187 ≤ (435794939023351/3125000000000000000 : ℝ)^1024 := by
      have hnat : (2851 : ℕ)^4187*3125000000000000000^1024 ≤ 435794939023351^1024*25000^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2851 25000 435794939023351 3125000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2851/25000 : ℝ)) (X := (435794939023351/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1759/12500 : ℝ) ^ (4187/1024 : ℝ) ≤ (6588250126051313/20000000000000000000 : ℝ) := by
    have hpowers : (1759/12500 : ℝ)^4187 ≤ (6588250126051313/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1759 : ℕ)^4187*20000000000000000000^1024 ≤ 6588250126051313^1024*12500^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1759 12500 6588250126051313 20000000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1759/12500 : ℝ)) (X := (6588250126051313/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562935794939023351/1562500000000000000 : ℝ) ≤ (5000341022794773/5000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (1562935794939023351/1562500000000000000 : ℝ)^1024 ≤ (5000341022794773/5000000000000000 : ℝ)^4187 := by
      have hnat : (1562935794939023351 : ℕ)^1024*5000000000000000^4187 ≤ 5000341022794773^4187*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562935794939023351 1562500000000000000 5000341022794773 5000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000341022794773/5000000000000000 : ℝ)) (X := (1562935794939023351/1562500000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046886688679003797/100000000000000000000 : ℝ) ≤ (10001146488384851/10000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (100046886688679003797/100000000000000000000 : ℝ)^1024 ≤ (10001146488384851/10000000000000000 : ℝ)^4187 := by
      have hnat : (100046886688679003797 : ℕ)^1024*10000000000000000^4187 ≤ 10001146488384851^4187*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046886688679003797 100000000000000000000 10001146488384851 10000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001146488384851/10000000000000000 : ℝ)) (X := (100046886688679003797/100000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006588250126051313/10000000000000000000 : ℝ) ≤ (2500402732795039/2500000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (10006588250126051313/10000000000000000000 : ℝ)^1024 ≤ (2500402732795039/2500000000000000 : ℝ)^4187 := by
      have hnat : (10006588250126051313 : ℕ)^1024*2500000000000000^4187 ≤ 2500402732795039^4187*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006588250126051313 10000000000000000000 2500402732795039 2500000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500402732795039/2500000000000000 : ℝ)) (X := (10006588250126051313/10000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(435794939023351/3125000000000000000 : ℝ) ≤ ((833475833948674759/833750000000000000 : ℝ)+2*(92888559061/53360000000000 : ℝ)*(2851/25000 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (833475833948674759/833750000000000000 : ℝ)+2*(92888559061/53360000000000 : ℝ)*(2851/25000 : ℝ)=(5000341022794773/5000000000000000 : ℝ) by norm_num, show 1+2*(435794939023351/3125000000000000000 : ℝ)=(1562935794939023351/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6588250126051313/20000000000000000000 : ℝ)+(435794939023351/3125000000000000000 : ℝ) ≤ ((833475833948674759/833750000000000000 : ℝ)+(92888559061/53360000000000 : ℝ)*((1759/12500 : ℝ)+(2851/25000 : ℝ)))^(4187/1024 : ℝ) := by
    rw [show (833475833948674759/833750000000000000 : ℝ)+(92888559061/53360000000000 : ℝ)*((1759/12500 : ℝ)+(2851/25000 : ℝ))=(10001146488384851/10000000000000000 : ℝ) by norm_num, show 1+(6588250126051313/20000000000000000000 : ℝ)+(435794939023351/3125000000000000000 : ℝ)=(100046886688679003797/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6588250126051313/20000000000000000000 : ℝ) ≤ ((833475833948674759/833750000000000000 : ℝ)+2*(92888559061/53360000000000 : ℝ)*(1759/12500 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (833475833948674759/833750000000000000 : ℝ)+2*(92888559061/53360000000000 : ℝ)*(1759/12500 : ℝ)=(2500402732795039/2500000000000000 : ℝ) by norm_num, show 1+2*(6588250126051313/20000000000000000000 : ℝ)=(10006588250126051313/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (833475833948674759/833750000000000000 : ℝ)*(X 1 0+X 2 0)+(92888559061/53360000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (833475833948674759/833750000000000000 : ℝ)) (alpha := (92888559061/53360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (833475833948674759/833750000000000000 : ℝ)*(X 0 1+X 2 1)+(92888559061/53360000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (833475833948674759/833750000000000000 : ℝ)) (alpha := (92888559061/53360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (833475833948674759/833750000000000000 : ℝ)*(X 0 2+X 1 2)+(92888559061/53360000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (833475833948674759/833750000000000000 : ℝ)) (alpha := (92888559061/53360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-134244199/625000000 : ℝ)*X 0 0+(107845273/200000000 : ℝ)*X 0 1+(5266402799/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672293303/5000000000 : ℝ)*X 1 0+(-34558367/156250000 : ℝ)*X 1 1+(1053280573/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344586607/10000000000 : ℝ)*X 2 0+(5266402847/10000000000 : ℝ)*X 2 1+(-2211735513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089767613/2500000000 : ℝ)*X 0 0+(4234689267/10000000000 : ℝ)*X 0 1+(4487052379/10000000000 : ℝ)*X 0 2+(1089767613/2500000000 : ℝ)*X 1 0+(4234689267/10000000000 : ℝ)*X 1 1+(4487052379/10000000000 : ℝ)*X 1 2+(1089767613/2500000000 : ℝ)*X 2 0+(4234689267/10000000000 : ℝ)*X 2 1+(4487052379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1073955991/5000000000 : ℝ)*X 0 0+(5266719281/10000000000 : ℝ)*X 0 1+(539194601/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212504251/400000000 : ℝ)*X 1 0+(-1043096139/5000000000 : ℝ)*X 1 1+(1078389201/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531260627/1000000000 : ℝ)*X 2 0+(2695973007/5000000000 : ℝ)*X 2 1+(-83447691/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089770001/2500000000 : ℝ)*X 0 0+(280401109/625000000 : ℝ)*X 0 1+(529415779/1250000000 : ℝ)*X 0 2+(1089770001/2500000000 : ℝ)*X 1 0+(280401109/625000000 : ℝ)*X 1 1+(529415779/1250000000 : ℝ)*X 1 2+(1089770001/2500000000 : ℝ)*X 2 0+(280401109/625000000 : ℝ)*X 2 1+(529415779/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (323522589822593028743885583/41687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (150527129/10000000000000 : ℝ)*(base19) + (712106967/50000000000000 : ℝ)*(base23) + (44116343/100000000000000 : ℝ)*(lower2) + (29021107/12500000000000 : ℝ)*(upper3) + (16593393/12500000000000 : ℝ)*(upper5) + (5953980844564777/100000000000000 : ℝ)*(major0) + (5953980844564777/100000000000000 : ℝ)*(major1) + (5953980844564777/100000000000000 : ℝ)*(major2) + (993166038311899/12500000000000 : ℝ)*(sp0) + (7945369241223057/100000000000000 : ℝ)*(sp1) + (1986342330570103/25000000000000 : ℝ)*(sp2) + (792513237484447/20000000000000 : ℝ)*(sp3) + (21219999577/50000000000000 : ℝ)*(sp4) + (12248262117/50000000000000 : ℝ)*(sp7) + (3962590683946469/100000000000000 : ℝ)*(f.failure) + (3972685373247173/50000000000000 : ℝ)*(f.sum) + (7904336001597/2668000000000000000000000000 : ℝ)*base65 + (172165373086327033/20843750000000000000000000000000 : ℝ)*base68 + (516457274382014533/20843750000000000000000000000000 : ℝ)*base70 + (31711280781983283/20843750000000000000000000000000 : ℝ)*base72 + (2189164043697/2668000000000000000000000000 : ℝ)*base73 + (759210681198233283/20843750000000000000000000000000 : ℝ)*base76 + (110587592639454217/20843750000000000000000000000000 : ℝ)*base77 + (371687456981014533/20843750000000000000000000000000 : ℝ)*base80 + (1791714826401/2668000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (64817157/10000000000000000000000 : ℝ)*base89 + (64817157/10000000000000000000000 : ℝ)*base91 + (64817157/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34673927398232826566395131/10421875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (845578249/100000000000000 : ℝ)*(base19) + (218379709/25000000000000 : ℝ)*(base23) + (289922227/100000000000000 : ℝ)*(lower1) + (14947213/100000000000000 : ℝ)*(upper2) + (95732051/100000000000000 : ℝ)*(upper3) + (45333459/50000000000000 : ℝ)*(upper5) + (748005743050757/12500000000000 : ℝ)*(major0) + (748005743050757/12500000000000 : ℝ)*(major1) + (748005743050757/12500000000000 : ℝ)*(major2) + (9501119/781250000000 : ℝ)*(sp2) + (62386653727579/781250000000 : ℝ)*(sp4) + (7985490831551863/100000000000000 : ℝ)*(sp5) + (1597097917493609/20000000000000 : ℝ)*(sp6) + (995650025195219/25000000000000 : ℝ)*(sp7) + (995650025195219/25000000000000 : ℝ)*(f.failure) + (62386653727579/781250000000 : ℝ)*(f.sum) + (394044852257/333500000000000000000000000 : ℝ)*base65 + (11225315669154203/2605468750000000000000000000000 : ℝ)*base68 + (34124361386779203/2605468750000000000000000000000 : ℝ)*base70 + (93374188278523813/10421875000000000000000000000000 : ℝ)*base71 + (224870901141/41687500000000000000000000 : ℝ)*base74 + (32319384579382437/10421875000000000000000000000000 : ℝ)*base76 + (25592755062949031/5210937500000000000000000000000 : ℝ)*base78 + (29426068678574031/5210937500000000000000000000000 : ℝ)*base80 + (6130768161407/667000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (7625907/2500000000000000000000 : ℝ)*base89 + (7625907/2500000000000000000000 : ℝ)*base91 + (7625907/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1182_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1182_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1182_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1182_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1182_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1182_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1182_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

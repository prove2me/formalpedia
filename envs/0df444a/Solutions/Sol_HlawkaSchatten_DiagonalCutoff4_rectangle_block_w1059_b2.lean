-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1059_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:02:20.625395+00:00
-- url     : https://prove2.me/submissions/7b7e69fc-9700-4864-bca0-ae0ade7cceeb

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
theorem support_rectangle_w1059_s6_0 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-551791999/2500000000 : ℝ)*x 0 + (2697531771/5000000000 : ℝ)*x 1 + (5263773017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551791999/2500000000 : ℝ)^2063 ≤ (837739833909/6250000000000 : ℝ)^1551 := by
    have hnat : (551791999 : ℕ)^2063*6250000000000^1551 ≤ 837739833909^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551791999 2500000000 837739833909 6250000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697531771/5000000000 : ℝ)^2063 ≤ (68761617041/156250000000 : ℝ)^1551 := by
    have hnat : (2697531771 : ℕ)^2063*156250000000^1551 ≤ 68761617041^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697531771 5000000000 68761617041 156250000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263773017/10000000000 : ℝ)^2063 ≤ (42588727731187/100000000000000 : ℝ)^1551 := by
    have hnat : (5263773017 : ℕ)^2063*100000000000000^1551 ≤ 42588727731187^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263773017 10000000000 42588727731187 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-551791999/2500000000 : ℝ), (2697531771/5000000000 : ℝ), (5263773017/10000000000 : ℝ)] ![(837739833909/6250000000000 : ℝ), (68761617041/156250000000 : ℝ), (42588727731187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-551791999/2500000000 : ℝ)|^2063 ≤ (837739833909/6250000000000 : ℝ)^1551
        have hw : |(-551791999/2500000000 : ℝ)|=(551791999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697531771/5000000000 : ℝ)|^2063 ≤ (68761617041/156250000000 : ℝ)^1551
        have hw : |(2697531771/5000000000 : ℝ)|=(2697531771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263773017/10000000000 : ℝ)|^2063 ≤ (42588727731187/100000000000000 : ℝ)^1551
        have hw : |(5263773017/10000000000 : ℝ)|=(5263773017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s6_1 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069028197/2000000000 : ℝ)*x 0 + (-2273790833/10000000000 : ℝ)*x 1 + (1315943261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069028197/2000000000 : ℝ)^2063 ≤ (43466620124189/100000000000000 : ℝ)^1551 := by
    have hnat : (1069028197 : ℕ)^2063*100000000000000^1551 ≤ 43466620124189^1551*2000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069028197 2000000000 43466620124189 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2273790833/10000000000 : ℝ)^2063 ≤ (13944651837499/100000000000000 : ℝ)^1551 := by
    have hnat : (2273790833 : ℕ)^2063*100000000000000^1551 ≤ 13944651837499^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273790833 10000000000 13944651837499 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315943261/2500000000 : ℝ)^2063 ≤ (10647182005439/25000000000000 : ℝ)^1551 := by
    have hnat : (1315943261 : ℕ)^2063*25000000000000^1551 ≤ 10647182005439^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315943261 2500000000 10647182005439 25000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069028197/2000000000 : ℝ), (-2273790833/10000000000 : ℝ), (1315943261/2500000000 : ℝ)] ![(43466620124189/100000000000000 : ℝ), (13944651837499/100000000000000 : ℝ), (10647182005439/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069028197/2000000000 : ℝ)|^2063 ≤ (43466620124189/100000000000000 : ℝ)^1551
        have hw : |(1069028197/2000000000 : ℝ)|=(1069028197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2273790833/10000000000 : ℝ)|^2063 ≤ (13944651837499/100000000000000 : ℝ)^1551
        have hw : |(-2273790833/10000000000 : ℝ)|=(2273790833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315943261/2500000000 : ℝ)|^2063 ≤ (10647182005439/25000000000000 : ℝ)^1551
        have hw : |(1315943261/2500000000 : ℝ)|=(1315943261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s6_2 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336285173/2500000000 : ℝ)*x 0 + (210550929/400000000 : ℝ)*x 1 + (-2273790983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336285173/2500000000 : ℝ)^2063 ≤ (21733308477487/50000000000000 : ℝ)^1551 := by
    have hnat : (1336285173 : ℕ)^2063*50000000000000^1551 ≤ 21733308477487^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336285173 2500000000 21733308477487 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210550929/400000000 : ℝ)^2063 ≤ (21294364984821/50000000000000 : ℝ)^1551 := by
    have hnat : (210550929 : ℕ)^2063*50000000000000^1551 ≤ 21294364984821^1551*400000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210550929 400000000 21294364984821 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273790983/10000000000 : ℝ)^2063 ≤ (13944653061089/100000000000000 : ℝ)^1551 := by
    have hnat : (2273790983 : ℕ)^2063*100000000000000^1551 ≤ 13944653061089^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273790983 10000000000 13944653061089 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336285173/2500000000 : ℝ), (210550929/400000000 : ℝ), (-2273790983/10000000000 : ℝ)] ![(21733308477487/50000000000000 : ℝ), (21294364984821/50000000000000 : ℝ), (13944653061089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336285173/2500000000 : ℝ)|^2063 ≤ (21733308477487/50000000000000 : ℝ)^1551
        have hw : |(1336285173/2500000000 : ℝ)|=(1336285173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210550929/400000000 : ℝ)|^2063 ≤ (21294364984821/50000000000000 : ℝ)^1551
        have hw : |(210550929/400000000 : ℝ)|=(210550929/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2273790983/10000000000 : ℝ)|^2063 ≤ (13944653061089/100000000000000 : ℝ)^1551
        have hw : |(-2273790983/10000000000 : ℝ)|=(2273790983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s6_3 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4376470829/10000000000 : ℝ)*x 0 + (531238441/1250000000 : ℝ)*x 1 + (2253430681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376470829/10000000000 : ℝ)^2063 ≤ (33316213415637/100000000000000 : ℝ)^1551 := by
    have hnat : (4376470829 : ℕ)^2063*100000000000000^1551 ≤ 33316213415637^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376470829 10000000000 33316213415637 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531238441/1250000000 : ℝ)^2063 ≤ (32040846177059/100000000000000 : ℝ)^1551 := by
    have hnat : (531238441 : ℕ)^2063*100000000000000^1551 ≤ 32040846177059^1551*1250000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531238441 1250000000 32040846177059 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253430681/5000000000 : ℝ)^2063 ≤ (34642940392981/100000000000000 : ℝ)^1551 := by
    have hnat : (2253430681 : ℕ)^2063*100000000000000^1551 ≤ 34642940392981^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253430681 5000000000 34642940392981 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376470829/10000000000 : ℝ), (531238441/1250000000 : ℝ), (2253430681/5000000000 : ℝ)] ![(33316213415637/100000000000000 : ℝ), (32040846177059/100000000000000 : ℝ), (34642940392981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376470829/10000000000 : ℝ)|^2063 ≤ (33316213415637/100000000000000 : ℝ)^1551
        have hw : |(4376470829/10000000000 : ℝ)|=(4376470829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(531238441/1250000000 : ℝ)|^2063 ≤ (32040846177059/100000000000000 : ℝ)^1551
        have hw : |(531238441/1250000000 : ℝ)|=(531238441/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253430681/5000000000 : ℝ)|^2063 ≤ (34642940392981/100000000000000 : ℝ)^1551
        have hw : |(2253430681/5000000000 : ℝ)|=(2253430681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s6_4 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2207173221/10000000000 : ℝ)*x 0 + (5264104721/10000000000 : ℝ)*x 1 + (5394730629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2207173221/10000000000 : ℝ)^2063 ≤ (13403879547909/100000000000000 : ℝ)^1551 := by
    have hnat : (2207173221 : ℕ)^2063*100000000000000^1551 ≤ 13403879547909^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207173221 10000000000 13403879547909 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264104721/10000000000 : ℝ)^2063 ≤ (266201859379/625000000000 : ℝ)^1551 := by
    have hnat : (5264104721 : ℕ)^2063*625000000000^1551 ≤ 266201859379^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264104721 10000000000 266201859379 625000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394730629/10000000000 : ℝ)^2063 ≤ (44003822943577/100000000000000 : ℝ)^1551 := by
    have hnat : (5394730629 : ℕ)^2063*100000000000000^1551 ≤ 44003822943577^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394730629 10000000000 44003822943577 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2207173221/10000000000 : ℝ), (5264104721/10000000000 : ℝ), (5394730629/10000000000 : ℝ)] ![(13403879547909/100000000000000 : ℝ), (266201859379/625000000000 : ℝ), (44003822943577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2207173221/10000000000 : ℝ)|^2063 ≤ (13403879547909/100000000000000 : ℝ)^1551
        have hw : |(-2207173221/10000000000 : ℝ)|=(2207173221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264104721/10000000000 : ℝ)|^2063 ≤ (266201859379/625000000000 : ℝ)^1551
        have hw : |(5264104721/10000000000 : ℝ)|=(5264104721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394730629/10000000000 : ℝ)|^2063 ≤ (44003822943577/100000000000000 : ℝ)^1551
        have hw : |(5394730629/10000000000 : ℝ)|=(5394730629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s6_5 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (16600281/31250000 : ℝ)*x 0 + (-428566651/2000000000 : ℝ)*x 1 + (269736537/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16600281/31250000 : ℝ)^2063 ≤ (21554745398773/50000000000000 : ℝ)^1551 := by
    have hnat : (16600281 : ℕ)^2063*50000000000000^1551 ≤ 21554745398773^1551*31250000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16600281 31250000 21554745398773 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428566651/2000000000 : ℝ)^2063 ≤ (6443342519017/50000000000000 : ℝ)^1551 := by
    have hnat : (428566651 : ℕ)^2063*50000000000000^1551 ≤ 6443342519017^1551*2000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428566651 2000000000 6443342519017 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269736537/500000000 : ℝ)^2063 ≤ (44003824147867/100000000000000 : ℝ)^1551 := by
    have hnat : (269736537 : ℕ)^2063*100000000000000^1551 ≤ 44003824147867^1551*500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269736537 500000000 44003824147867 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16600281/31250000 : ℝ), (-428566651/2000000000 : ℝ), (269736537/500000000 : ℝ)] ![(21554745398773/50000000000000 : ℝ), (6443342519017/50000000000000 : ℝ), (44003824147867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16600281/31250000 : ℝ)|^2063 ≤ (21554745398773/50000000000000 : ℝ)^1551
        have hw : |(16600281/31250000 : ℝ)|=(16600281/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-428566651/2000000000 : ℝ)|^2063 ≤ (6443342519017/50000000000000 : ℝ)^1551
        have hw : |(-428566651/2000000000 : ℝ)|=(428566651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269736537/500000000 : ℝ)|^2063 ≤ (44003824147867/100000000000000 : ℝ)^1551
        have hw : |(269736537/500000000 : ℝ)|=(269736537/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s6_6 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312089747/10000000000 : ℝ)*x 0 + (5394730939/10000000000 : ℝ)*x 1 + (-2142833219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312089747/10000000000 : ℝ)^2063 ≤ (4310948893013/10000000000000 : ℝ)^1551 := by
    have hnat : (5312089747 : ℕ)^2063*10000000000000^1551 ≤ 4310948893013^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312089747 10000000000 4310948893013 10000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394730939/10000000000 : ℝ)^2063 ≤ (44003826306909/100000000000000 : ℝ)^1551 := by
    have hnat : (5394730939 : ℕ)^2063*100000000000000^1551 ≤ 44003826306909^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394730939 10000000000 44003826306909 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2142833219/10000000000 : ℝ)^2063 ≤ (12886684750067/100000000000000 : ℝ)^1551 := by
    have hnat : (2142833219 : ℕ)^2063*100000000000000^1551 ≤ 12886684750067^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142833219 10000000000 12886684750067 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312089747/10000000000 : ℝ), (5394730939/10000000000 : ℝ), (-2142833219/10000000000 : ℝ)] ![(4310948893013/10000000000000 : ℝ), (44003826306909/100000000000000 : ℝ), (12886684750067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312089747/10000000000 : ℝ)|^2063 ≤ (4310948893013/10000000000000 : ℝ)^1551
        have hw : |(5312089747/10000000000 : ℝ)|=(5312089747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394730939/10000000000 : ℝ)|^2063 ≤ (44003826306909/100000000000000 : ℝ)^1551
        have hw : |(5394730939/10000000000 : ℝ)|=(5394730939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2142833219/10000000000 : ℝ)|^2063 ≤ (12886684750067/100000000000000 : ℝ)^1551
        have hw : |(-2142833219/10000000000 : ℝ)|=(2142833219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s6_7 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (875296227/2000000000 : ℝ)*x 0 + (4506212137/10000000000 : ℝ)*x 1 + (2125279509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875296227/2000000000 : ℝ)^2063 ≤ (33316317769693/100000000000000 : ℝ)^1551 := by
    have hnat : (875296227 : ℕ)^2063*100000000000000^1551 ≤ 33316317769693^1551*2000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875296227 2000000000 33316317769693 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506212137/10000000000 : ℝ)^2063 ≤ (1385452110613/4000000000000 : ℝ)^1551 := by
    have hnat : (4506212137 : ℕ)^2063*4000000000000^1551 ≤ 1385452110613^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506212137 10000000000 1385452110613 4000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125279509/5000000000 : ℝ)^2063 ≤ (32047379447991/100000000000000 : ℝ)^1551 := by
    have hnat : (2125279509 : ℕ)^2063*100000000000000^1551 ≤ 32047379447991^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125279509 5000000000 32047379447991 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875296227/2000000000 : ℝ), (4506212137/10000000000 : ℝ), (2125279509/5000000000 : ℝ)] ![(33316317769693/100000000000000 : ℝ), (1385452110613/4000000000000 : ℝ), (32047379447991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875296227/2000000000 : ℝ)|^2063 ≤ (33316317769693/100000000000000 : ℝ)^1551
        have hw : |(875296227/2000000000 : ℝ)|=(875296227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506212137/10000000000 : ℝ)|^2063 ≤ (1385452110613/4000000000000 : ℝ)^1551
        have hw : |(4506212137/10000000000 : ℝ)|=(4506212137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2125279509/5000000000 : ℝ)|^2063 ≤ (32047379447991/100000000000000 : ℝ)^1551
        have hw : |(2125279509/5000000000 : ℝ)|=(2125279509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1059_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11187/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1123/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14011/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1757/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11187/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1757/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11187/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1757/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11187/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1757/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11187/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1757/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11187/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1757/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11187/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11187/100000 : ℝ) ^ (8251/2048 : ℝ) ≤ (7352234226926177/50000000000000000000 : ℝ) := by
    have hpowers : (11187/100000 : ℝ)^8251 ≤ (7352234226926177/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11187 : ℕ)^8251*50000000000000000000^2048 ≤ 7352234226926177^2048*100000^8251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11187 100000 7352234226926177 50000000000000000000 8251 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11187/100000 : ℝ)) (X := (7352234226926177/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1757/12500 : ℝ) ^ (8251/2048 : ℝ) ≤ (18444551255606991/50000000000000000000 : ℝ) := by
    have hpowers : (1757/12500 : ℝ)^8251 ≤ (18444551255606991/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1757 : ℕ)^8251*50000000000000000000^2048 ≤ 18444551255606991^2048*12500^8251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1757 12500 18444551255606991 50000000000000000000 8251 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1757/12500 : ℝ)) (X := (18444551255606991/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007352234226926177/25000000000000000000 : ℝ) ≤ (10000729885417243/10000000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (25007352234226926177/25000000000000000000 : ℝ)^2048 ≤ (10000729885417243/10000000000000000 : ℝ)^8251 := by
      have hnat : (25007352234226926177 : ℕ)^2048*10000000000000000^8251 ≤ 10000729885417243^8251*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007352234226926177 25000000000000000000 10000729885417243 10000000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000729885417243/10000000000000000 : ℝ)) (X := (25007352234226926177/25000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126612299092658323/3125000000000000000 : ℝ) ≤ (10001280367802867/10000000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (3126612299092658323/3125000000000000000 : ℝ)^2048 ≤ (10001280367802867/10000000000000000 : ℝ)^8251 := by
      have hnat : (3126612299092658323 : ℕ)^2048*10000000000000000^8251 ≤ 10001280367802867^8251*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126612299092658323 3125000000000000000 10001280367802867 10000000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001280367802867/10000000000000000 : ℝ)) (X := (3126612299092658323/3125000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018444551255606991/25000000000000000000 : ℝ) ≤ (10001830850188491/10000000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (25018444551255606991/25000000000000000000 : ℝ)^2048 ≤ (10001830850188491/10000000000000000 : ℝ)^8251 := by
      have hnat : (25018444551255606991 : ℕ)^2048*10000000000000000^8251 ≤ 10001830850188491^8251*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018444551255606991 25000000000000000000 10001830850188491 10000000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001830850188491/10000000000000000 : ℝ)) (X := (25018444551255606991/25000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7352234226926177/50000000000000000000 : ℝ) ≤ ((28679777548366118791/28690000000000000000 : ℝ)+2*(68810298203/35862500000000 : ℝ)*(11187/100000 : ℝ))^(8251/2048 : ℝ) := by
    rw [show (28679777548366118791/28690000000000000000 : ℝ)+2*(68810298203/35862500000000 : ℝ)*(11187/100000 : ℝ)=(10000729885417243/10000000000000000 : ℝ) by norm_num, show 1+2*(7352234226926177/50000000000000000000 : ℝ)=(25007352234226926177/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18444551255606991/50000000000000000000 : ℝ)+(7352234226926177/50000000000000000000 : ℝ) ≤ ((28679777548366118791/28690000000000000000 : ℝ)+(68810298203/35862500000000 : ℝ)*((1757/12500 : ℝ)+(11187/100000 : ℝ)))^(8251/2048 : ℝ) := by
    rw [show (28679777548366118791/28690000000000000000 : ℝ)+(68810298203/35862500000000 : ℝ)*((1757/12500 : ℝ)+(11187/100000 : ℝ))=(10001280367802867/10000000000000000 : ℝ) by norm_num, show 1+(18444551255606991/50000000000000000000 : ℝ)+(7352234226926177/50000000000000000000 : ℝ)=(3126612299092658323/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18444551255606991/50000000000000000000 : ℝ) ≤ ((28679777548366118791/28690000000000000000 : ℝ)+2*(68810298203/35862500000000 : ℝ)*(1757/12500 : ℝ))^(8251/2048 : ℝ) := by
    rw [show (28679777548366118791/28690000000000000000 : ℝ)+2*(68810298203/35862500000000 : ℝ)*(1757/12500 : ℝ)=(10001830850188491/10000000000000000 : ℝ) by norm_num, show 1+2*(18444551255606991/50000000000000000000 : ℝ)=(25018444551255606991/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28679777548366118791/28690000000000000000 : ℝ)*(X 1 0+X 2 0)+(68810298203/35862500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (11187/100000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (28679777548366118791/28690000000000000000 : ℝ)) (alpha := (68810298203/35862500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28679777548366118791/28690000000000000000 : ℝ)*(X 0 1+X 2 1)+(68810298203/35862500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (11187/100000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (28679777548366118791/28690000000000000000 : ℝ)) (alpha := (68810298203/35862500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28679777548366118791/28690000000000000000 : ℝ)*(X 0 2+X 1 2)+(68810298203/35862500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (11187/100000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (28679777548366118791/28690000000000000000 : ℝ)) (alpha := (68810298203/35862500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-551791999/2500000000 : ℝ)*X 0 0+(2697531771/5000000000 : ℝ)*X 0 1+(5263773017/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069028197/2000000000 : ℝ)*X 1 0+(-2273790833/10000000000 : ℝ)*X 1 1+(1315943261/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336285173/2500000000 : ℝ)*X 2 0+(210550929/400000000 : ℝ)*X 2 1+(-2273790983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4376470829/10000000000 : ℝ)*X 0 0+(531238441/1250000000 : ℝ)*X 0 1+(2253430681/5000000000 : ℝ)*X 0 2+(4376470829/10000000000 : ℝ)*X 1 0+(531238441/1250000000 : ℝ)*X 1 1+(2253430681/5000000000 : ℝ)*X 1 2+(4376470829/10000000000 : ℝ)*X 2 0+(531238441/1250000000 : ℝ)*X 2 1+(2253430681/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2207173221/10000000000 : ℝ)*X 0 0+(5264104721/10000000000 : ℝ)*X 0 1+(5394730629/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((16600281/31250000 : ℝ)*X 1 0+(-428566651/2000000000 : ℝ)*X 1 1+(269736537/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312089747/10000000000 : ℝ)*X 2 0+(5394730939/10000000000 : ℝ)*X 2 1+(-2142833219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((875296227/2000000000 : ℝ)*X 0 0+(4506212137/10000000000 : ℝ)*X 0 1+(2125279509/5000000000 : ℝ)*X 0 2+(875296227/2000000000 : ℝ)*X 1 0+(4506212137/10000000000 : ℝ)*X 1 1+(2125279509/5000000000 : ℝ)*X 1 2+(875296227/2000000000 : ℝ)*X 2 0+(4506212137/10000000000 : ℝ)*X 2 1+(2125279509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (86258698441249185960261/14345000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1420884443/100000000000000 : ℝ)*(base19) + (503113211/50000000000000 : ℝ)*(base23) + (323449/6250000000000 : ℝ)*(upper2) + (310992267/100000000000000 : ℝ)*(upper3) + (455539/12500000000000 : ℝ)*(upper4) + (5754283015522277/100000000000000 : ℝ)*(major0) + (5754283015522277/100000000000000 : ℝ)*(major1) + (5754283015522277/100000000000000 : ℝ)*(major2) + (3808372082890523/50000000000000 : ℝ)*(sp0) + (7616771955580499/100000000000000 : ℝ)*(sp1) + (190419309255963/2500000000000 : ℝ)*(sp2) + (194588450582393/5000000000000 : ℝ)*(sp3) + (29210683897/100000000000000 : ℝ)*(sp4) + (23442493269/100000000000000 : ℝ)*(sp7) + (3891792454141129/100000000000000 : ℝ)*(f.failure) + (7616773376464943/100000000000000 : ℝ)*(f.sum) + (12363129899079/7172500000000000000000000000 : ℝ)*base65 + (4053932011735607107/2869000000000000000000000000000000 : ℝ)*base67 + (18580049537559392893/2869000000000000000000000000000000 : ℝ)*base70 + (2192481091256392893/2869000000000000000000000000000000 : ℝ)*base72 + (33279791559961/7172500000000000000000000000 : ℝ)*base74 + (13302386213668392893/2869000000000000000000000000000000 : ℝ)*base76 + (2609638700318607107/2869000000000000000000000000000000 : ℝ)*base77 + (11587856206096607107/2869000000000000000000000000000000 : ℝ)*base79 + (6792680933579/7172500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (76040907/10000000000000000000000 : ℝ)*base89 + (76040907/10000000000000000000000 : ℝ)*base91 + (76040907/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (337713508638296031409816203/44828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39204539/2500000000000 : ℝ)*(base19) + (707704171/50000000000000 : ℝ)*(base23) + (247322641/100000000000000 : ℝ)*(upper3) + (8340767/25000000000000 : ℝ)*(lower4) + (167097813/100000000000000 : ℝ)*(upper5) + (90367131021681/1562500000000 : ℝ)*(major0) + (90367131021681/1562500000000 : ℝ)*(major1) + (90367131021681/1562500000000 : ℝ)*(major2) + (42749881719/100000000000000 : ℝ)*(sp1) + (24086219207/50000000000000 : ℝ)*(sp2) + (7655442196101019/100000000000000 : ℝ)*(sp4) + (7655397878037741/100000000000000 : ℝ)*(sp5) + (1531078521650853/20000000000000 : ℝ)*(sp6) + (1955775161778429/50000000000000 : ℝ)*(sp7) + (1955775161778429/50000000000000 : ℝ)*(f.failure) + (7655442196101019/100000000000000 : ℝ)*(f.sum) + (89424768404279/14345000000000000000000000000 : ℝ)*base66 + (15479944166741477/22414062500000000000000000000000 : ℝ)*base68 + (15936933640025213/5603515625000000000000000000000 : ℝ)*base70 + (247718804017366477/22414062500000000000000000000000 : ℝ)*base72 + (2362313600333/1793125000000000000000000000 : ℝ)*base74 + (8074690084654829/44828125000000000000000000000000 : ℝ)*base76 + (129732064552147727/22414062500000000000000000000000 : ℝ)*base78 + (30980126845462713/5603515625000000000000000000000 : ℝ)*base80 + (86990991005201/14345000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/50000000000000 : ℝ)*base87 + (48576807/5000000000000000000000 : ℝ)*base89 + (48576807/5000000000000000000000 : ℝ)*base91 + (48576807/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1059_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11187/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1059_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1059_s7_0 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2207210143/10000000000 : ℝ)*x 0 + (539458289/1000000000 : ℝ)*x 1 + (2632112973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2207210143/10000000000 : ℝ)^2063 ≤ (335104444733/2500000000000 : ℝ)^1551 := by
    have hnat : (2207210143 : ℕ)^2063*2500000000000^1551 ≤ 335104444733^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207210143 10000000000 335104444733 2500000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539458289/1000000000 : ℝ)^2063 ≤ (44002220062631/100000000000000 : ℝ)^1551 := by
    have hnat : (539458289 : ℕ)^2063*100000000000000^1551 ≤ 44002220062631^1551*1000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539458289 1000000000 44002220062631 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632112973/5000000000 : ℝ)^2063 ≤ (42593602132021/100000000000000 : ℝ)^1551 := by
    have hnat : (2632112973 : ℕ)^2063*100000000000000^1551 ≤ 42593602132021^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632112973 5000000000 42593602132021 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2207210143/10000000000 : ℝ), (539458289/1000000000 : ℝ), (2632112973/5000000000 : ℝ)] ![(335104444733/2500000000000 : ℝ), (44002220062631/100000000000000 : ℝ), (42593602132021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2207210143/10000000000 : ℝ)|^2063 ≤ (335104444733/2500000000000 : ℝ)^1551
        have hw : |(-2207210143/10000000000 : ℝ)|=(2207210143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539458289/1000000000 : ℝ)|^2063 ≤ (44002220062631/100000000000000 : ℝ)^1551
        have hw : |(539458289/1000000000 : ℝ)|=(539458289/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632112973/5000000000 : ℝ)|^2063 ≤ (42593602132021/100000000000000 : ℝ)^1551
        have hw : |(2632112973/5000000000 : ℝ)|=(2632112973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s7_1 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069004187/2000000000 : ℝ)*x 0 + (-2273351979/10000000000 : ℝ)*x 1 + (526422633/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069004187/2000000000 : ℝ)^2063 ≤ (8693064323201/20000000000000 : ℝ)^1551 := by
    have hnat : (1069004187 : ℕ)^2063*20000000000000^1551 ≤ 8693064323201^1551*2000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069004187 2000000000 8693064323201 20000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2273351979/10000000000 : ℝ)^2063 ≤ (697053605149/5000000000000 : ℝ)^1551 := by
    have hnat : (2273351979 : ℕ)^2063*5000000000000^1551 ≤ 697053605149^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273351979 10000000000 697053605149 5000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526422633/1000000000 : ℝ)^2063 ≤ (4259360626467/10000000000000 : ℝ)^1551 := by
    have hnat : (526422633 : ℕ)^2063*10000000000000^1551 ≤ 4259360626467^1551*1000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526422633 1000000000 4259360626467 10000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069004187/2000000000 : ℝ), (-2273351979/10000000000 : ℝ), (526422633/1000000000 : ℝ)] ![(8693064323201/20000000000000 : ℝ), (697053605149/5000000000000 : ℝ), (4259360626467/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069004187/2000000000 : ℝ)|^2063 ≤ (8693064323201/20000000000000 : ℝ)^1551
        have hw : |(1069004187/2000000000 : ℝ)|=(1069004187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2273351979/10000000000 : ℝ)|^2063 ≤ (697053605149/5000000000000 : ℝ)^1551
        have hw : |(-2273351979/10000000000 : ℝ)|=(2273351979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526422633/1000000000 : ℝ)|^2063 ≤ (4259360626467/10000000000000 : ℝ)^1551
        have hw : |(526422633/1000000000 : ℝ)|=(526422633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s7_2 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345021071/10000000000 : ℝ)*x 0 + (329014127/625000000 : ℝ)*x 1 + (-4440141/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345021071/10000000000 : ℝ)^2063 ≤ (43465323087029/100000000000000 : ℝ)^1551 := by
    have hnat : (5345021071 : ℕ)^2063*100000000000000^1551 ≤ 43465323087029^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345021071 10000000000 43465323087029 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329014127/625000000 : ℝ)^2063 ≤ (21296801528781/50000000000000 : ℝ)^1551 := by
    have hnat : (329014127 : ℕ)^2063*50000000000000^1551 ≤ 21296801528781^1551*625000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329014127 625000000 21296801528781 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4440141/19531250 : ℝ)^2063 ≤ (13941073840367/100000000000000 : ℝ)^1551 := by
    have hnat : (4440141 : ℕ)^2063*100000000000000^1551 ≤ 13941073840367^1551*19531250^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4440141 19531250 13941073840367 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345021071/10000000000 : ℝ), (329014127/625000000 : ℝ), (-4440141/19531250 : ℝ)] ![(43465323087029/100000000000000 : ℝ), (21296801528781/50000000000000 : ℝ), (13941073840367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345021071/10000000000 : ℝ)|^2063 ≤ (43465323087029/100000000000000 : ℝ)^1551
        have hw : |(5345021071/10000000000 : ℝ)|=(5345021071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329014127/625000000 : ℝ)|^2063 ≤ (21296801528781/50000000000000 : ℝ)^1551
        have hw : |(329014127/625000000 : ℝ)|=(329014127/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4440141/19531250 : ℝ)|^2063 ≤ (13941073840367/100000000000000 : ℝ)^1551
        have hw : |(-4440141/19531250 : ℝ)|=(4440141/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s7_3 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2188247361/5000000000 : ℝ)*x 0 + (4250818609/10000000000 : ℝ)*x 1 + (4505944041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188247361/5000000000 : ℝ)^2063 ≤ (33316455345847/100000000000000 : ℝ)^1551 := by
    have hnat : (2188247361 : ℕ)^2063*100000000000000^1551 ≤ 33316455345847^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188247361 5000000000 33316455345847 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4250818609/10000000000 : ℝ)^2063 ≤ (32049982770127/100000000000000 : ℝ)^1551 := by
    have hnat : (4250818609 : ℕ)^2063*100000000000000^1551 ≤ 32049982770127^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250818609 10000000000 32049982770127 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505944041/10000000000 : ℝ)^2063 ≤ (34633561864043/100000000000000 : ℝ)^1551 := by
    have hnat : (4505944041 : ℕ)^2063*100000000000000^1551 ≤ 34633561864043^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505944041 10000000000 34633561864043 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188247361/5000000000 : ℝ), (4250818609/10000000000 : ℝ), (4505944041/10000000000 : ℝ)] ![(33316455345847/100000000000000 : ℝ), (32049982770127/100000000000000 : ℝ), (34633561864043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188247361/5000000000 : ℝ)|^2063 ≤ (33316455345847/100000000000000 : ℝ)^1551
        have hw : |(2188247361/5000000000 : ℝ)|=(2188247361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4250818609/10000000000 : ℝ)|^2063 ≤ (32049982770127/100000000000000 : ℝ)^1551
        have hw : |(4250818609/10000000000 : ℝ)|=(4250818609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505944041/10000000000 : ℝ)|^2063 ≤ (34633561864043/100000000000000 : ℝ)^1551
        have hw : |(4505944041/10000000000 : ℝ)|=(4505944041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s7_4 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1103607569/5000000000 : ℝ)*x 0 + (1316138261/2500000000 : ℝ)*x 1 + (5394254697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103607569/5000000000 : ℝ)^2063 ≤ (6702109068547/50000000000000 : ℝ)^1551 := by
    have hnat : (1103607569 : ℕ)^2063*50000000000000^1551 ≤ 6702109068547^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103607569 5000000000 6702109068547 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316138261/2500000000 : ℝ)^2063 ≤ (2129856121579/5000000000000 : ℝ)^1551 := by
    have hnat : (1316138261 : ℕ)^2063*5000000000000^1551 ≤ 2129856121579^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316138261 2500000000 2129856121579 5000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394254697/10000000000 : ℝ)^2063 ≤ (10999664853537/25000000000000 : ℝ)^1551 := by
    have hnat : (5394254697 : ℕ)^2063*25000000000000^1551 ≤ 10999664853537^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394254697 10000000000 10999664853537 25000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1103607569/5000000000 : ℝ), (1316138261/2500000000 : ℝ), (5394254697/10000000000 : ℝ)] ![(6702109068547/50000000000000 : ℝ), (2129856121579/5000000000000 : ℝ), (10999664853537/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1103607569/5000000000 : ℝ)|^2063 ≤ (6702109068547/50000000000000 : ℝ)^1551
        have hw : |(-1103607569/5000000000 : ℝ)|=(1103607569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316138261/2500000000 : ℝ)|^2063 ≤ (2129856121579/5000000000000 : ℝ)^1551
        have hw : |(1316138261/2500000000 : ℝ)|=(1316138261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394254697/10000000000 : ℝ)|^2063 ≤ (10999664853537/25000000000000 : ℝ)^1551
        have hw : |(5394254697/10000000000 : ℝ)|=(5394254697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s7_5 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312205611/10000000000 : ℝ)*x 0 + (-2143323803/10000000000 : ℝ)*x 1 + (2697126973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312205611/10000000000 : ℝ)^2063 ≤ (2694421225413/6250000000000 : ℝ)^1551 := by
    have hnat : (5312205611 : ℕ)^2063*6250000000000^1551 ≤ 2694421225413^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312205611 10000000000 2694421225413 6250000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2143323803/10000000000 : ℝ)^2063 ≤ (6445304560517/50000000000000 : ℝ)^1551 := by
    have hnat : (2143323803 : ℕ)^2063*50000000000000^1551 ≤ 6445304560517^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143323803 10000000000 6445304560517 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697126973/5000000000 : ℝ)^2063 ≤ (21999325633221/50000000000000 : ℝ)^1551 := by
    have hnat : (2697126973 : ℕ)^2063*50000000000000^1551 ≤ 21999325633221^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697126973 5000000000 21999325633221 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312205611/10000000000 : ℝ), (-2143323803/10000000000 : ℝ), (2697126973/5000000000 : ℝ)] ![(2694421225413/6250000000000 : ℝ), (6445304560517/50000000000000 : ℝ), (21999325633221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312205611/10000000000 : ℝ)|^2063 ≤ (2694421225413/6250000000000 : ℝ)^1551
        have hw : |(5312205611/10000000000 : ℝ)|=(5312205611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2143323803/10000000000 : ℝ)|^2063 ≤ (6445304560517/50000000000000 : ℝ)^1551
        have hw : |(-2143323803/10000000000 : ℝ)|=(2143323803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697126973/5000000000 : ℝ)|^2063 ≤ (21999325633221/50000000000000 : ℝ)^1551
        have hw : |(2697126973/5000000000 : ℝ)|=(2697126973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s7_6 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062441099/2000000000 : ℝ)*x 0 + (5394254209/10000000000 : ℝ)*x 1 + (-1071661801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062441099/2000000000 : ℝ)^2063 ≤ (43110738354459/100000000000000 : ℝ)^1551 := by
    have hnat : (1062441099 : ℕ)^2063*100000000000000^1551 ≤ 43110738354459^1551*2000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062441099 2000000000 43110738354459 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394254209/10000000000 : ℝ)^2063 ≤ (43998654119767/100000000000000 : ℝ)^1551 := by
    have hnat : (5394254209 : ℕ)^2063*100000000000000^1551 ≤ 43998654119767^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394254209 10000000000 43998654119767 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1071661801/5000000000 : ℝ)^2063 ≤ (1611325939137/12500000000000 : ℝ)^1551 := by
    have hnat : (1071661801 : ℕ)^2063*12500000000000^1551 ≤ 1611325939137^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071661801 5000000000 1611325939137 12500000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062441099/2000000000 : ℝ), (5394254209/10000000000 : ℝ), (-1071661801/5000000000 : ℝ)] ![(43110738354459/100000000000000 : ℝ), (43998654119767/100000000000000 : ℝ), (1611325939137/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062441099/2000000000 : ℝ)|^2063 ≤ (43110738354459/100000000000000 : ℝ)^1551
        have hw : |(1062441099/2000000000 : ℝ)|=(1062441099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394254209/10000000000 : ℝ)|^2063 ≤ (43998654119767/100000000000000 : ℝ)^1551
        have hw : |(5394254209/10000000000 : ℝ)|=(5394254209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1071661801/5000000000 : ℝ)|^2063 ≤ (1611325939137/12500000000000 : ℝ)^1551
        have hw : |(-1071661801/5000000000 : ℝ)|=(1071661801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s7_7 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4376503877/10000000000 : ℝ)*x 0 + (4505305159/10000000000 : ℝ)*x 1 + (1062865157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376503877/10000000000 : ℝ)^2063 ≤ (16658274022771/50000000000000 : ℝ)^1551 := by
    have hnat : (4376503877 : ℕ)^2063*50000000000000^1551 ≤ 16658274022771^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376503877 10000000000 16658274022771 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505305159/10000000000 : ℝ)^2063 ≤ (34627030418907/100000000000000 : ℝ)^1551 := by
    have hnat : (4505305159 : ℕ)^2063*100000000000000^1551 ≤ 34627030418907^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505305159 10000000000 34627030418907 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062865157/2500000000 : ℝ)^2063 ≤ (16028210758591/50000000000000 : ℝ)^1551 := by
    have hnat : (1062865157 : ℕ)^2063*50000000000000^1551 ≤ 16028210758591^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062865157 2500000000 16028210758591 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376503877/10000000000 : ℝ), (4505305159/10000000000 : ℝ), (1062865157/2500000000 : ℝ)] ![(16658274022771/50000000000000 : ℝ), (34627030418907/100000000000000 : ℝ), (16028210758591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376503877/10000000000 : ℝ)|^2063 ≤ (16658274022771/50000000000000 : ℝ)^1551
        have hw : |(4376503877/10000000000 : ℝ)|=(4376503877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505305159/10000000000 : ℝ)|^2063 ≤ (34627030418907/100000000000000 : ℝ)^1551
        have hw : |(4505305159/10000000000 : ℝ)|=(4505305159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1062865157/2500000000 : ℝ)|^2063 ≤ (16028210758591/50000000000000 : ℝ)^1551
        have hw : |(1062865157/2500000000 : ℝ)|=(1062865157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1059_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (281/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14001/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14011/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1123/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14011/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1123/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14011/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1123/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14011/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1123/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14011/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1123/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14011/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1123/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1123/10000 : ℝ) ^ (8251/2048 : ℝ) ≤ (14933506703111059/100000000000000000000 : ℝ) := by
    have hpowers : (1123/10000 : ℝ)^8251 ≤ (14933506703111059/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1123 : ℕ)^8251*100000000000000000000^2048 ≤ 14933506703111059^2048*10000^8251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1123 10000 14933506703111059 100000000000000000000 8251 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1123/10000 : ℝ)) (X := (14933506703111059/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14011/100000 : ℝ) ^ (8251/2048 : ℝ) ≤ (36415603211981641/100000000000000000000 : ℝ) := by
    have hpowers : (14011/100000 : ℝ)^8251 ≤ (36415603211981641/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14011 : ℕ)^8251*100000000000000000000^2048 ≤ 36415603211981641^2048*100000^8251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14011 100000 36415603211981641 100000000000000000000 8251 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14011/100000 : ℝ)) (X := (36415603211981641/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014933506703111059/50000000000000000000 : ℝ) ≤ (2500185313227089/2500000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (50014933506703111059/50000000000000000000 : ℝ)^2048 ≤ (2500185313227089/2500000000000000 : ℝ)^8251 := by
      have hnat : (50014933506703111059 : ℕ)^2048*2500000000000000^8251 ≤ 2500185313227089^8251*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014933506703111059 50000000000000000000 2500185313227089 2500000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500185313227089/2500000000000000 : ℝ)) (X := (50014933506703111059/50000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1000513491099150927/1000000000000000000 : ℝ) ≤ (10001274302324911/10000000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (1000513491099150927/1000000000000000000 : ℝ)^2048 ≤ (10001274302324911/10000000000000000 : ℝ)^8251 := by
      have hnat : (1000513491099150927 : ℕ)^2048*10000000000000000^8251 ≤ 10001274302324911^8251*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000513491099150927 1000000000000000000 10001274302324911 10000000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001274302324911/10000000000000000 : ℝ)) (X := (1000513491099150927/1000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036415603211981641/50000000000000000000 : ℝ) ≤ (5000903675870733/5000000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (50036415603211981641/50000000000000000000 : ℝ)^2048 ≤ (5000903675870733/5000000000000000 : ℝ)^8251 := by
      have hnat : (50036415603211981641 : ℕ)^2048*5000000000000000^8251 ≤ 5000903675870733^8251*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036415603211981641 50000000000000000000 5000903675870733 5000000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000903675870733/5000000000000000 : ℝ)) (X := (50036415603211981641/50000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14933506703111059/100000000000000000000 : ℝ) ≤ ((868752785451322273/869062500000000000 : ℝ)+2*(106609883311/55620000000000 : ℝ)*(1123/10000 : ℝ))^(8251/2048 : ℝ) := by
    rw [show (868752785451322273/869062500000000000 : ℝ)+2*(106609883311/55620000000000 : ℝ)*(1123/10000 : ℝ)=(2500185313227089/2500000000000000 : ℝ) by norm_num, show 1+2*(14933506703111059/100000000000000000000 : ℝ)=(50014933506703111059/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36415603211981641/100000000000000000000 : ℝ)+(14933506703111059/100000000000000000000 : ℝ) ≤ ((868752785451322273/869062500000000000 : ℝ)+(106609883311/55620000000000 : ℝ)*((14011/100000 : ℝ)+(1123/10000 : ℝ)))^(8251/2048 : ℝ) := by
    rw [show (868752785451322273/869062500000000000 : ℝ)+(106609883311/55620000000000 : ℝ)*((14011/100000 : ℝ)+(1123/10000 : ℝ))=(10001274302324911/10000000000000000 : ℝ) by norm_num, show 1+(36415603211981641/100000000000000000000 : ℝ)+(14933506703111059/100000000000000000000 : ℝ)=(1000513491099150927/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36415603211981641/100000000000000000000 : ℝ) ≤ ((868752785451322273/869062500000000000 : ℝ)+2*(106609883311/55620000000000 : ℝ)*(14011/100000 : ℝ))^(8251/2048 : ℝ) := by
    rw [show (868752785451322273/869062500000000000 : ℝ)+2*(106609883311/55620000000000 : ℝ)*(14011/100000 : ℝ)=(5000903675870733/5000000000000000 : ℝ) by norm_num, show 1+2*(36415603211981641/100000000000000000000 : ℝ)=(50036415603211981641/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (868752785451322273/869062500000000000 : ℝ)*(X 1 0+X 2 0)+(106609883311/55620000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (1123/10000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (868752785451322273/869062500000000000 : ℝ)) (alpha := (106609883311/55620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (868752785451322273/869062500000000000 : ℝ)*(X 0 1+X 2 1)+(106609883311/55620000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (1123/10000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (868752785451322273/869062500000000000 : ℝ)) (alpha := (106609883311/55620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (868752785451322273/869062500000000000 : ℝ)*(X 0 2+X 1 2)+(106609883311/55620000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (1123/10000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (868752785451322273/869062500000000000 : ℝ)) (alpha := (106609883311/55620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2207210143/10000000000 : ℝ)*X 0 0+(539458289/1000000000 : ℝ)*X 0 1+(2632112973/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069004187/2000000000 : ℝ)*X 1 0+(-2273351979/10000000000 : ℝ)*X 1 1+(526422633/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345021071/10000000000 : ℝ)*X 2 0+(329014127/625000000 : ℝ)*X 2 1+(-4440141/19531250 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2188247361/5000000000 : ℝ)*X 0 0+(4250818609/10000000000 : ℝ)*X 0 1+(4505944041/10000000000 : ℝ)*X 0 2+(2188247361/5000000000 : ℝ)*X 1 0+(4250818609/10000000000 : ℝ)*X 1 1+(4505944041/10000000000 : ℝ)*X 1 2+(2188247361/5000000000 : ℝ)*X 2 0+(4250818609/10000000000 : ℝ)*X 2 1+(4505944041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1103607569/5000000000 : ℝ)*X 0 0+(1316138261/2500000000 : ℝ)*X 0 1+(5394254697/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312205611/10000000000 : ℝ)*X 1 0+(-2143323803/10000000000 : ℝ)*X 1 1+(2697126973/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062441099/2000000000 : ℝ)*X 2 0+(5394254209/10000000000 : ℝ)*X 2 1+(-1071661801/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4376503877/10000000000 : ℝ)*X 0 0+(4505305159/10000000000 : ℝ)*X 0 1+(1062865157/2500000000 : ℝ)*X 0 2+(4376503877/10000000000 : ℝ)*X 1 0+(4505305159/10000000000 : ℝ)*X 1 1+(1062865157/2500000000 : ℝ)*X 1 2+(4376503877/10000000000 : ℝ)*X 2 0+(4505305159/10000000000 : ℝ)*X 2 1+(1062865157/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (235125631114262399416191/160937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (159035607/20000000000000 : ℝ)*(base19) + (280043933/25000000000000 : ℝ)*(base23) + (115652467/100000000000000 : ℝ)*(upper2) + (50567761/25000000000000 : ℝ)*(upper3) + (46270541/100000000000000 : ℝ)*(upper4) + (1159099256329447/20000000000000 : ℝ)*(major0) + (1159099256329447/20000000000000 : ℝ)*(major1) + (1159099256329447/20000000000000 : ℝ)*(major2) + (61370321957711/800000000000 : ℝ)*(sp0) + (958915688716301/12500000000000 : ℝ)*(sp1) + (7671325184732711/100000000000000 : ℝ)*(sp2) + (1959825577292637/50000000000000 : ℝ)*(sp3) + (36060194569/100000000000000 : ℝ)*(sp4) + (7527550793/50000000000000 : ℝ)*(sp7) + (195983310484343/5000000000000 : ℝ)*(f.failure) + (7671326304908443/100000000000000 : ℝ)*(f.sum) + (5830599707821/1390500000000000000000000000 : ℝ)*base65 + (45795065286775289/4345312500000000000000000000000 : ℝ)*base67 + (12898007791383797/8690625000000000000000000000000 : ℝ)*base70 + (27576467467206539/4345312500000000000000000000000 : ℝ)*base71 + (9823181103763/2781000000000000000000000000 : ℝ)*base74 + (9576937499687789/4345312500000000000000000000000 : ℝ)*base75 + (134829784231972453/8690625000000000000000000000000 : ℝ)*base77 + (27837466470382957/2172656250000000000000000000000 : ℝ)*base79 + (1326055838009/556200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1282869/500000000000000000000 : ℝ)*base89 + (1282869/500000000000000000000 : ℝ)*base91 + (1282869/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6722850363137202250692139/1207031250000000000000000000000 : ℝ) := by norm_num
    linear_combination (80756449/4000000000000 : ℝ)*(base19) + (690450151/25000000000000 : ℝ)*(base23) + (94290227/25000000000000 : ℝ)*(upper2) + (23082581/50000000000000 : ℝ)*(lower5) + (5824705133163003/100000000000000 : ℝ)*(major0) + (5824705133163003/100000000000000 : ℝ)*(major1) + (5824705133163003/100000000000000 : ℝ)*(major2) + (26981888489/100000000000000 : ℝ)*(sp1) + (59561650669/100000000000000 : ℝ)*(sp2) + (438040893/20000000000000 : ℝ)*(sp3) + (963748632182419/12500000000000 : ℝ)*(sp4) + (3854980028329819/50000000000000 : ℝ)*(sp5) + (7709926734008079/100000000000000 : ℝ)*(sp6) + (157576753320167/4000000000000 : ℝ)*(sp7) + (3939421023208641/100000000000000 : ℝ)*(f.failure) + (963748632182419/12500000000000 : ℝ)*(f.sum) + (1356110702057/231750000000000000000000000 : ℝ)*base65 + (25385361108644287/7242187500000000000000000000000 : ℝ)*base67 + (293571636798585449/14484375000000000000000000000000 : ℝ)*base69 + (66322762077550537/7242187500000000000000000000000 : ℝ)*base71 + (254261029561/231750000000000000000000000 : ℝ)*base74 + (433120325515804199/14484375000000000000000000000000 : ℝ)*base75 + (81326013728272949/14484375000000000000000000000000 : ℝ)*base77 + (25453447943272949/14484375000000000000000000000000 : ℝ)*base79 + (2592768958159/463500000000000000000000000 : ℝ)*base81 + (16926003/10000000000000000000000 : ℝ)*base89 + (16926003/10000000000000000000000 : ℝ)*base91 + (16926003/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1059_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1123/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1059_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1059_s8_0 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-551804443/2500000000 : ℝ)*x 0 + (337154743/625000000 : ℝ)*x 1 + (5264328089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551804443/2500000000 : ℝ)^2063 ≤ (1340423941359/10000000000000 : ℝ)^1551 := by
    have hnat : (551804443 : ℕ)^2063*10000000000000^1551 ≤ 1340423941359^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551804443 2500000000 1340423941359 10000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337154743/625000000 : ℝ)^2063 ≤ (44001059163137/100000000000000 : ℝ)^1551 := by
    have hnat : (337154743 : ℕ)^2063*100000000000000^1551 ≤ 44001059163137^1551*625000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337154743 625000000 44001059163137 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264328089/10000000000 : ℝ)^2063 ≤ (5324337676171/12500000000000 : ℝ)^1551 := by
    have hnat : (5264328089 : ℕ)^2063*12500000000000^1551 ≤ 5324337676171^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264328089 10000000000 5324337676171 12500000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-551804443/2500000000 : ℝ), (337154743/625000000 : ℝ), (5264328089/10000000000 : ℝ)] ![(1340423941359/10000000000000 : ℝ), (44001059163137/100000000000000 : ℝ), (5324337676171/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-551804443/2500000000 : ℝ)|^2063 ≤ (1340423941359/10000000000000 : ℝ)^1551
        have hw : |(-551804443/2500000000 : ℝ)|=(551804443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337154743/625000000 : ℝ)|^2063 ≤ (44001059163137/100000000000000 : ℝ)^1551
        have hw : |(337154743/625000000 : ℝ)|=(337154743/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264328089/10000000000 : ℝ)|^2063 ≤ (5324337676171/12500000000000 : ℝ)^1551
        have hw : |(5264328089/10000000000 : ℝ)|=(5264328089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s8_1 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534499471/1000000000 : ℝ)*x 0 + (-2273252489/10000000000 : ℝ)*x 1 + (1316082023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534499471/1000000000 : ℝ)^2063 ≤ (8693007591467/20000000000000 : ℝ)^1551 := by
    have hnat : (534499471 : ℕ)^2063*20000000000000^1551 ≤ 8693007591467^1551*1000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534499471 1000000000 8693007591467 20000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2273252489/10000000000 : ℝ)^2063 ≤ (6970130297107/50000000000000 : ℝ)^1551 := by
    have hnat : (2273252489 : ℕ)^2063*50000000000000^1551 ≤ 6970130297107^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273252489 10000000000 6970130297107 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316082023/2500000000 : ℝ)^2063 ≤ (8518940288331/20000000000000 : ℝ)^1551 := by
    have hnat : (1316082023 : ℕ)^2063*20000000000000^1551 ≤ 8518940288331^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316082023 2500000000 8518940288331 20000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534499471/1000000000 : ℝ), (-2273252489/10000000000 : ℝ), (1316082023/2500000000 : ℝ)] ![(8693007591467/20000000000000 : ℝ), (6970130297107/50000000000000 : ℝ), (8518940288331/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534499471/1000000000 : ℝ)|^2063 ≤ (8693007591467/20000000000000 : ℝ)^1551
        have hw : |(534499471/1000000000 : ℝ)|=(534499471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2273252489/10000000000 : ℝ)|^2063 ≤ (6970130297107/50000000000000 : ℝ)^1551
        have hw : |(-2273252489/10000000000 : ℝ)|=(2273252489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316082023/2500000000 : ℝ)|^2063 ≤ (8518940288331/20000000000000 : ℝ)^1551
        have hw : |(1316082023/2500000000 : ℝ)|=(1316082023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s8_2 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344994693/10000000000 : ℝ)*x 0 + (5264328083/10000000000 : ℝ)*x 1 + (-2273252523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344994693/10000000000 : ℝ)^2063 ≤ (43465037773457/100000000000000 : ℝ)^1551 := by
    have hnat : (5344994693 : ℕ)^2063*100000000000000^1551 ≤ 43465037773457^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344994693 10000000000 43465037773457 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264328083/10000000000 : ℝ)^2063 ≤ (8518940268959/20000000000000 : ℝ)^1551 := by
    have hnat : (5264328083 : ℕ)^2063*20000000000000^1551 ≤ 8518940268959^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264328083 10000000000 8518940268959 20000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273252523/10000000000 : ℝ)^2063 ≤ (13940260871539/100000000000000 : ℝ)^1551 := by
    have hnat : (2273252523 : ℕ)^2063*100000000000000^1551 ≤ 13940260871539^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273252523 10000000000 13940260871539 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344994693/10000000000 : ℝ), (5264328083/10000000000 : ℝ), (-2273252523/10000000000 : ℝ)] ![(43465037773457/100000000000000 : ℝ), (8518940268959/20000000000000 : ℝ), (13940260871539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344994693/10000000000 : ℝ)|^2063 ≤ (43465037773457/100000000000000 : ℝ)^1551
        have hw : |(5344994693/10000000000 : ℝ)|=(5344994693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264328083/10000000000 : ℝ)|^2063 ≤ (8518940268959/20000000000000 : ℝ)^1551
        have hw : |(5264328083/10000000000 : ℝ)|=(5264328083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2273252523/10000000000 : ℝ)|^2063 ≤ (13940260871539/100000000000000 : ℝ)^1551
        have hw : |(-2273252523/10000000000 : ℝ)|=(2273252523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s8_3 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (875300019/2000000000 : ℝ)*x 0 + (2125511007/5000000000 : ℝ)*x 1 + (4505739189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875300019/2000000000 : ℝ)^2063 ≤ (33316509750587/100000000000000 : ℝ)^1551 := by
    have hnat : (875300019 : ℕ)^2063*100000000000000^1551 ≤ 33316509750587^1551*2000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875300019 2000000000 33316509750587 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125511007/5000000000 : ℝ)^2063 ≤ (32052022664649/100000000000000 : ℝ)^1551 := by
    have hnat : (2125511007 : ℕ)^2063*100000000000000^1551 ≤ 32052022664649^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125511007 5000000000 32052022664649 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505739189/10000000000 : ℝ)^2063 ≤ (17315733789613/50000000000000 : ℝ)^1551 := by
    have hnat : (4505739189 : ℕ)^2063*50000000000000^1551 ≤ 17315733789613^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505739189 10000000000 17315733789613 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875300019/2000000000 : ℝ), (2125511007/5000000000 : ℝ), (4505739189/10000000000 : ℝ)] ![(33316509750587/100000000000000 : ℝ), (32052022664649/100000000000000 : ℝ), (17315733789613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875300019/2000000000 : ℝ)|^2063 ≤ (33316509750587/100000000000000 : ℝ)^1551
        have hw : |(875300019/2000000000 : ℝ)|=(875300019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2125511007/5000000000 : ℝ)|^2063 ≤ (32052022664649/100000000000000 : ℝ)^1551
        have hw : |(2125511007/5000000000 : ℝ)|=(2125511007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505739189/10000000000 : ℝ)|^2063 ≤ (17315733789613/50000000000000 : ℝ)^1551
        have hw : |(4505739189/10000000000 : ℝ)|=(4505739189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s8_4 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-551805711/2500000000 : ℝ)*x 0 + (5264653919/10000000000 : ℝ)*x 1 + (5394148891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551805711/2500000000 : ℝ)^2063 ≤ (13404280383389/100000000000000 : ℝ)^1551 := by
    have hnat : (551805711 : ℕ)^2063*100000000000000^1551 ≤ 13404280383389^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551805711 2500000000 13404280383389 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264653919/10000000000 : ℝ)^2063 ≤ (42598208084757/100000000000000 : ℝ)^1551 := by
    have hnat : (5264653919 : ℕ)^2063*100000000000000^1551 ≤ 42598208084757^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264653919 10000000000 42598208084757 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394148891/10000000000 : ℝ)^2063 ≤ (2199875575673/5000000000000 : ℝ)^1551 := by
    have hnat : (5394148891 : ℕ)^2063*5000000000000^1551 ≤ 2199875575673^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394148891 10000000000 2199875575673 5000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-551805711/2500000000 : ℝ), (5264653919/10000000000 : ℝ), (5394148891/10000000000 : ℝ)] ![(13404280383389/100000000000000 : ℝ), (42598208084757/100000000000000 : ℝ), (2199875575673/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-551805711/2500000000 : ℝ)|^2063 ≤ (13404280383389/100000000000000 : ℝ)^1551
        have hw : |(-551805711/2500000000 : ℝ)|=(551805711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264653919/10000000000 : ℝ)|^2063 ≤ (42598208084757/100000000000000 : ℝ)^1551
        have hw : |(5264653919/10000000000 : ℝ)|=(5264653919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394148891/10000000000 : ℝ)|^2063 ≤ (2199875575673/5000000000000 : ℝ)^1551
        have hw : |(5394148891/10000000000 : ℝ)|=(5394148891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s8_5 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656115651/5000000000 : ℝ)*x 0 + (-107171581/500000000 : ℝ)*x 1 + (5394148883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656115651/5000000000 : ℝ)^2063 ≤ (43111016925453/100000000000000 : ℝ)^1551 := by
    have hnat : (2656115651 : ℕ)^2063*100000000000000^1551 ≤ 43111016925453^1551*5000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656115651 5000000000 43111016925453 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107171581/500000000 : ℝ)^2063 ≤ (6445735815311/50000000000000 : ℝ)^1551 := by
    have hnat : (107171581 : ℕ)^2063*50000000000000^1551 ≤ 6445735815311^1551*500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107171581 500000000 6445735815311 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394148883/10000000000 : ℝ)^2063 ≤ (10999377856667/25000000000000 : ℝ)^1551 := by
    have hnat : (5394148883 : ℕ)^2063*25000000000000^1551 ≤ 10999377856667^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394148883 10000000000 10999377856667 25000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656115651/5000000000 : ℝ), (-107171581/500000000 : ℝ), (5394148883/10000000000 : ℝ)] ![(43111016925453/100000000000000 : ℝ), (6445735815311/50000000000000 : ℝ), (10999377856667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656115651/5000000000 : ℝ)|^2063 ≤ (43111016925453/100000000000000 : ℝ)^1551
        have hw : |(2656115651/5000000000 : ℝ)|=(2656115651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-107171581/500000000 : ℝ)|^2063 ≤ (6445735815311/50000000000000 : ℝ)^1551
        have hw : |(-107171581/500000000 : ℝ)|=(107171581/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394148883/10000000000 : ℝ)|^2063 ≤ (10999377856667/25000000000000 : ℝ)^1551
        have hw : |(5394148883/10000000000 : ℝ)|=(5394148883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s8_6 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312231103/10000000000 : ℝ)*x 0 + (5394148839/10000000000 : ℝ)*x 1 + (-535857987/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312231103/10000000000 : ℝ)^2063 ≤ (43111014777367/100000000000000 : ℝ)^1551 := by
    have hnat : (5312231103 : ℕ)^2063*100000000000000^1551 ≤ 43111014777367^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312231103 10000000000 43111014777367 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394148839/10000000000 : ℝ)^2063 ≤ (43997510949309/100000000000000 : ℝ)^1551 := by
    have hnat : (5394148839 : ℕ)^2063*100000000000000^1551 ≤ 43997510949309^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394148839 10000000000 43997510949309 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535857987/2500000000 : ℝ)^2063 ≤ (3222868563641/25000000000000 : ℝ)^1551 := by
    have hnat : (535857987 : ℕ)^2063*25000000000000^1551 ≤ 3222868563641^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535857987 2500000000 3222868563641 25000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312231103/10000000000 : ℝ), (5394148839/10000000000 : ℝ), (-535857987/2500000000 : ℝ)] ![(43111014777367/100000000000000 : ℝ), (43997510949309/100000000000000 : ℝ), (3222868563641/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312231103/10000000000 : ℝ)|^2063 ≤ (43111014777367/100000000000000 : ℝ)^1551
        have hw : |(5312231103/10000000000 : ℝ)|=(5312231103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394148839/10000000000 : ℝ)|^2063 ≤ (43997510949309/100000000000000 : ℝ)^1551
        have hw : |(5394148839/10000000000 : ℝ)|=(5394148839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-535857987/2500000000 : ℝ)|^2063 ≤ (3222868563641/25000000000000 : ℝ)^1551
        have hw : |(-535857987/2500000000 : ℝ)|=(535857987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1059_s8_7 (p : ℝ) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1094127451/2500000000 : ℝ)*x 0 + (281568841/625000000 : ℝ)*x 1 + (4251662281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094127451/2500000000 : ℝ)^2063 ≤ (4164576007487/12500000000000 : ℝ)^1551 := by
    have hnat : (1094127451 : ℕ)^2063*12500000000000^1551 ≤ 4164576007487^1551*2500000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094127451 2500000000 4164576007487 12500000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281568841/625000000 : ℝ)^2063 ≤ (17312473989087/50000000000000 : ℝ)^1551 := by
    have hnat : (281568841 : ℕ)^2063*50000000000000^1551 ≤ 17312473989087^1551*625000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281568841 625000000 17312473989087 50000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4251662281/10000000000 : ℝ)^2063 ≤ (32058443942047/100000000000000 : ℝ)^1551 := by
    have hnat : (4251662281 : ℕ)^2063*100000000000000^1551 ≤ 32058443942047^1551*10000000000^2063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251662281 10000000000 32058443942047 100000000000000 2063 1551 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2063/512 : ℝ)) 2063 1551 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094127451/2500000000 : ℝ), (281568841/625000000 : ℝ), (4251662281/10000000000 : ℝ)] ![(4164576007487/12500000000000 : ℝ), (17312473989087/50000000000000 : ℝ), (32058443942047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094127451/2500000000 : ℝ)|^2063 ≤ (4164576007487/12500000000000 : ℝ)^1551
        have hw : |(1094127451/2500000000 : ℝ)|=(1094127451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281568841/625000000 : ℝ)|^2063 ≤ (17312473989087/50000000000000 : ℝ)^1551
        have hw : |(281568841/625000000 : ℝ)|=(281568841/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4251662281/10000000000 : ℝ)|^2063 ≤ (32058443942047/100000000000000 : ℝ)^1551
        have hw : |(4251662281/10000000000 : ℝ)|=(4251662281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1059_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (5621/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13999/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (281/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (281/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (281/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (281/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (281/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (281/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (281/2500 : ℝ) ^ (8251/2048 : ℝ) ≤ (7493576781015197/50000000000000000000 : ℝ) := by
    have hpowers : (281/2500 : ℝ)^8251 ≤ (7493576781015197/50000000000000000000 : ℝ)^2048 := by
      have hnat : (281 : ℕ)^8251*50000000000000000000^2048 ≤ 7493576781015197^2048*2500^8251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        281 2500 7493576781015197 50000000000000000000 8251 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (281/2500 : ℝ)) (X := (7493576781015197/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14001/100000 : ℝ) ^ (8251/2048 : ℝ) ≤ (4538875585646091/12500000000000000000 : ℝ) := by
    have hpowers : (14001/100000 : ℝ)^8251 ≤ (4538875585646091/12500000000000000000 : ℝ)^2048 := by
      have hnat : (14001 : ℕ)^8251*12500000000000000000^2048 ≤ 4538875585646091^2048*100000^8251 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14001 100000 4538875585646091 12500000000000000000 8251 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14001/100000 : ℝ)) (X := (4538875585646091/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007493576781015197/25000000000000000000 : ℝ) ≤ (2500185978867979/2500000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (25007493576781015197/25000000000000000000 : ℝ)^2048 ≤ (2500185978867979/2500000000000000 : ℝ)^8251 := by
      have hnat : (25007493576781015197 : ℕ)^2048*2500000000000000^8251 ≤ 2500185978867979^8251*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007493576781015197 25000000000000000000 2500185978867979 2500000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500185978867979/2500000000000000 : ℝ)) (X := (25007493576781015197/25000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025649079123599561/50000000000000000000 : ℝ) ≤ (10001273038129403/10000000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (50025649079123599561/50000000000000000000 : ℝ)^2048 ≤ (10001273038129403/10000000000000000 : ℝ)^8251 := by
      have hnat : (50025649079123599561 : ℕ)^2048*10000000000000000^8251 ≤ 10001273038129403^8251*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025649079123599561 50000000000000000000 10001273038129403 10000000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001273038129403/10000000000000000 : ℝ)) (X := (50025649079123599561/50000000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254538875585646091/6250000000000000000 : ℝ) ≤ (1000180216078689/1000000000000000 : ℝ) ^ (8251/2048 : ℝ) := by
    have hpowers : (6254538875585646091/6250000000000000000 : ℝ)^2048 ≤ (1000180216078689/1000000000000000 : ℝ)^8251 := by
      have hnat : (6254538875585646091 : ℕ)^2048*1000000000000000^8251 ≤ 1000180216078689^8251*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254538875585646091 6250000000000000000 1000180216078689 1000000000000000 2048 8251 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000180216078689/1000000000000000 : ℝ)) (X := (6254538875585646091/6250000000000000000 : ℝ)) (by norm_num) 8251 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7493576781015197/50000000000000000000 : ℝ) ≤ ((6900039818319413079/6902500000000000000 : ℝ)+2*(529122657487/276100000000000 : ℝ)*(281/2500 : ℝ))^(8251/2048 : ℝ) := by
    rw [show (6900039818319413079/6902500000000000000 : ℝ)+2*(529122657487/276100000000000 : ℝ)*(281/2500 : ℝ)=(2500185978867979/2500000000000000 : ℝ) by norm_num, show 1+2*(7493576781015197/50000000000000000000 : ℝ)=(25007493576781015197/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4538875585646091/12500000000000000000 : ℝ)+(7493576781015197/50000000000000000000 : ℝ) ≤ ((6900039818319413079/6902500000000000000 : ℝ)+(529122657487/276100000000000 : ℝ)*((14001/100000 : ℝ)+(281/2500 : ℝ)))^(8251/2048 : ℝ) := by
    rw [show (6900039818319413079/6902500000000000000 : ℝ)+(529122657487/276100000000000 : ℝ)*((14001/100000 : ℝ)+(281/2500 : ℝ))=(10001273038129403/10000000000000000 : ℝ) by norm_num, show 1+(4538875585646091/12500000000000000000 : ℝ)+(7493576781015197/50000000000000000000 : ℝ)=(50025649079123599561/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4538875585646091/12500000000000000000 : ℝ) ≤ ((6900039818319413079/6902500000000000000 : ℝ)+2*(529122657487/276100000000000 : ℝ)*(14001/100000 : ℝ))^(8251/2048 : ℝ) := by
    rw [show (6900039818319413079/6902500000000000000 : ℝ)+2*(529122657487/276100000000000 : ℝ)*(14001/100000 : ℝ)=(1000180216078689/1000000000000000 : ℝ) by norm_num, show 1+2*(4538875585646091/12500000000000000000 : ℝ)=(6254538875585646091/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6900039818319413079/6902500000000000000 : ℝ)*(X 1 0+X 2 0)+(529122657487/276100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (6900039818319413079/6902500000000000000 : ℝ)) (alpha := (529122657487/276100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6900039818319413079/6902500000000000000 : ℝ)*(X 0 1+X 2 1)+(529122657487/276100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (6900039818319413079/6902500000000000000 : ℝ)) (alpha := (529122657487/276100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6900039818319413079/6902500000000000000 : ℝ)*(X 0 2+X 1 2)+(529122657487/276100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8251/2048 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (14001/100000 : ℝ)) (c := (6900039818319413079/6902500000000000000 : ℝ)) (alpha := (529122657487/276100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-551804443/2500000000 : ℝ)*X 0 0+(337154743/625000000 : ℝ)*X 0 1+(5264328089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534499471/1000000000 : ℝ)*X 1 0+(-2273252489/10000000000 : ℝ)*X 1 1+(1316082023/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344994693/10000000000 : ℝ)*X 2 0+(5264328083/10000000000 : ℝ)*X 2 1+(-2273252523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((875300019/2000000000 : ℝ)*X 0 0+(2125511007/5000000000 : ℝ)*X 0 1+(4505739189/10000000000 : ℝ)*X 0 2+(875300019/2000000000 : ℝ)*X 1 0+(2125511007/5000000000 : ℝ)*X 1 1+(4505739189/10000000000 : ℝ)*X 1 2+(875300019/2000000000 : ℝ)*X 2 0+(2125511007/5000000000 : ℝ)*X 2 1+(4505739189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-551805711/2500000000 : ℝ)*X 0 0+(5264653919/10000000000 : ℝ)*X 0 1+(5394148891/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656115651/5000000000 : ℝ)*X 1 0+(-107171581/500000000 : ℝ)*X 1 1+(5394148883/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312231103/10000000000 : ℝ)*X 2 0+(5394148839/10000000000 : ℝ)*X 2 1+(-535857987/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1094127451/2500000000 : ℝ)*X 0 0+(281568841/625000000 : ℝ)*X 0 1+(4251662281/10000000000 : ℝ)*X 0 2+(1094127451/2500000000 : ℝ)*X 1 0+(281568841/625000000 : ℝ)*X 1 1+(4251662281/10000000000 : ℝ)*X 1 2+(1094127451/2500000000 : ℝ)*X 2 0+(281568841/625000000 : ℝ)*X 2 1+(4251662281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1059_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1545175877844212087286783153/345125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (469601649/50000000000000 : ℝ)*(base19) + (215316019/25000000000000 : ℝ)*(base23) + (5719263/20000000000000 : ℝ)*(lower2) + (70456383/50000000000000 : ℝ)*(upper3) + (21355603/50000000000000 : ℝ)*(upper5) + (5804786468262823/100000000000000 : ℝ)*(major0) + (5804786468262823/100000000000000 : ℝ)*(major1) + (5804786468262823/100000000000000 : ℝ)*(major2) + (7683599764648777/100000000000000 : ℝ)*(sp0) + (7683622409353607/100000000000000 : ℝ)*(sp1) + (768362248729283/10000000000000 : ℝ)*(sp2) + (245370942826781/6250000000000 : ℝ)*(sp3) + (23583908129/100000000000000 : ℝ)*(sp4) + (2870700389/20000000000000 : ℝ)*(sp7) + (98148735968261/2500000000000 : ℝ)*(f.failure) + (1536724669711381/20000000000000 : ℝ)*(f.sum) + (82500341939099/13805000000000000000000000000 : ℝ)*base66 + (14220796693917062983/690250000000000000000000000000000 : ℝ)*base68 + (19746771836764562983/690250000000000000000000000000000 : ℝ)*base70 + (4965824938296812983/690250000000000000000000000000000 : ℝ)*base72 + (24189718921301/3451250000000000000000000000 : ℝ)*base74 + (27629285854582562983/690250000000000000000000000000000 : ℝ)*base76 + (6589660303151812983/690250000000000000000000000000000 : ℝ)*base78 + (11889510701477812983/690250000000000000000000000000000 : ℝ)*base80 + (35854790560697/6902500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (890463/250000000000000000000 : ℝ)*base89 + (890463/250000000000000000000 : ℝ)*base91 + (890463/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (986470154707232680964059761/86281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2086397973/100000000000000 : ℝ)*(base19) + (164871023/10000000000000 : ℝ)*(base23) + (97959629/20000000000000 : ℝ)*(lower1) + (1221639/20000000000000 : ℝ)*(upper2) + (128404611/100000000000000 : ℝ)*(upper3) + (14539559/6250000000000 : ℝ)*(upper5) + (1458495802129051/25000000000000 : ℝ)*(major0) + (1458495802129051/25000000000000 : ℝ)*(major1) + (1458495802129051/25000000000000 : ℝ)*(major2) + (25926761527/100000000000000 : ℝ)*(sp1) + (1544453994976019/20000000000000 : ℝ)*(sp4) + (1930560490430149/25000000000000 : ℝ)*(sp5) + (1544453665233973/20000000000000 : ℝ)*(sp6) + (3945696061045873/100000000000000 : ℝ)*(sp7) + (3945696061045873/100000000000000 : ℝ)*(f.failure) + (1544453994976019/20000000000000 : ℝ)*(f.sum) + (12477199387453/3451250000000000000000000000 : ℝ)*base66 + (3432454001823379471/172562500000000000000000000000000 : ℝ)*base68 + (1310160888508691971/172562500000000000000000000000000 : ℝ)*base70 + (2466574003574691971/172562500000000000000000000000000 : ℝ)*base72 + (12656758008023/13805000000000000000000000000 : ℝ)*base73 + (6580251753597879471/172562500000000000000000000000000 : ℝ)*base76 + (4298927690325504471/172562500000000000000000000000000 : ℝ)*base78 + (1173558146900254471/172562500000000000000000000000000 : ℝ)*base80 + (575518160329483/13805000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (101793859/10000000000000000000000 : ℝ)*base89 + (101793859/10000000000000000000000 : ℝ)*base91 + (101793859/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1059_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5621/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1059_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1059_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11187/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5621/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1059_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1059_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1059_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8251/2048 : ℝ) ≤ p) (hpb : p ≤ (2063/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147856883/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11187/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5621/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13999/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1059_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

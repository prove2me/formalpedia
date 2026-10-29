-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1607_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:50:55.786973+00:00
-- url     : https://prove2.me/submissions/1e285c77-de20-4dcc-b15b-4469aed456fd

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
theorem support_rectangle_w1607_s3_0 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1711735483/10000000000 : ℝ)*x 0 + (5460995901/10000000000 : ℝ)*x 1 + (647496041/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1711735483/10000000000 : ℝ)^4747 ≤ (526702894439/5000000000000 : ℝ)^3723 := by
    have hnat : (1711735483 : ℕ)^4747*5000000000000^3723 ≤ 526702894439^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1711735483 10000000000 526702894439 5000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5460995901/10000000000 : ℝ)^4747 ≤ (46239088025223/100000000000000 : ℝ)^3723 := by
    have hnat : (5460995901 : ℕ)^4747*100000000000000^3723 ≤ 46239088025223^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460995901 10000000000 46239088025223 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647496041/1250000000 : ℝ)^4747 ≤ (21613427035187/50000000000000 : ℝ)^3723 := by
    have hnat : (647496041 : ℕ)^4747*50000000000000^3723 ≤ 21613427035187^3723*1250000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647496041 1250000000 21613427035187 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1711735483/10000000000 : ℝ), (5460995901/10000000000 : ℝ), (647496041/1250000000 : ℝ)] ![(526702894439/5000000000000 : ℝ), (46239088025223/100000000000000 : ℝ), (21613427035187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1711735483/10000000000 : ℝ)|^4747 ≤ (526702894439/5000000000000 : ℝ)^3723
        have hw : |(-1711735483/10000000000 : ℝ)|=(1711735483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5460995901/10000000000 : ℝ)|^4747 ≤ (46239088025223/100000000000000 : ℝ)^3723
        have hw : |(5460995901/10000000000 : ℝ)|=(5460995901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647496041/1250000000 : ℝ)|^4747 ≤ (21613427035187/50000000000000 : ℝ)^3723
        have hw : |(647496041/1250000000 : ℝ)|=(647496041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s3_1 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133853851/250000000 : ℝ)*x 0 + (-928342131/5000000000 : ℝ)*x 1 + (5179968329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133853851/250000000 : ℝ)^4747 ≤ (22544369827157/50000000000000 : ℝ)^3723 := by
    have hnat : (133853851 : ℕ)^4747*50000000000000^3723 ≤ 22544369827157^3723*250000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133853851 250000000 22544369827157 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (928342131/5000000000 : ℝ)^4747 ≤ (146055078199/1250000000000 : ℝ)^3723 := by
    have hnat : (928342131 : ℕ)^4747*1250000000000^3723 ≤ 146055078199^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928342131 5000000000 146055078199 1250000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179968329/10000000000 : ℝ)^4747 ≤ (8645370816203/20000000000000 : ℝ)^3723 := by
    have hnat : (5179968329 : ℕ)^4747*20000000000000^3723 ≤ 8645370816203^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179968329 10000000000 8645370816203 20000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133853851/250000000 : ℝ), (-928342131/5000000000 : ℝ), (5179968329/10000000000 : ℝ)] ![(22544369827157/50000000000000 : ℝ), (146055078199/1250000000000 : ℝ), (8645370816203/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133853851/250000000 : ℝ)|^4747 ≤ (22544369827157/50000000000000 : ℝ)^3723
        have hw : |(133853851/250000000 : ℝ)|=(133853851/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-928342131/5000000000 : ℝ)|^4747 ≤ (146055078199/1250000000000 : ℝ)^3723
        have hw : |(-928342131/5000000000 : ℝ)|=(928342131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179968329/10000000000 : ℝ)|^4747 ≤ (8645370816203/20000000000000 : ℝ)^3723
        have hw : |(5179968329/10000000000 : ℝ)|=(5179968329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s3_2 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677077021/5000000000 : ℝ)*x 0 + (647496041/1250000000 : ℝ)*x 1 + (-1856684261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677077021/5000000000 : ℝ)^4747 ≤ (45088739675789/100000000000000 : ℝ)^3723 := by
    have hnat : (2677077021 : ℕ)^4747*100000000000000^3723 ≤ 45088739675789^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677077021 5000000000 45088739675789 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647496041/1250000000 : ℝ)^4747 ≤ (21613427035187/50000000000000 : ℝ)^3723 := by
    have hnat : (647496041 : ℕ)^4747*50000000000000^3723 ≤ 21613427035187^3723*1250000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647496041 1250000000 21613427035187 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1856684261/10000000000 : ℝ)^4747 ≤ (1460550780987/12500000000000 : ℝ)^3723 := by
    have hnat : (1856684261 : ℕ)^4747*12500000000000^3723 ≤ 1460550780987^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856684261 10000000000 1460550780987 12500000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677077021/5000000000 : ℝ), (647496041/1250000000 : ℝ), (-1856684261/10000000000 : ℝ)] ![(45088739675789/100000000000000 : ℝ), (21613427035187/50000000000000 : ℝ), (1460550780987/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677077021/5000000000 : ℝ)|^4747 ≤ (45088739675789/100000000000000 : ℝ)^3723
        have hw : |(2677077021/5000000000 : ℝ)|=(2677077021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647496041/1250000000 : ℝ)|^4747 ≤ (21613427035187/50000000000000 : ℝ)^3723
        have hw : |(647496041/1250000000 : ℝ)|=(647496041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1856684261/10000000000 : ℝ)|^4747 ≤ (1460550780987/12500000000000 : ℝ)^3723
        have hw : |(-1856684261/10000000000 : ℝ)|=(1856684261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s3_3 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84298883/200000000 : ℝ)*x 0 + (3881872687/10000000000 : ℝ)*x 1 + (114243153/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84298883/200000000 : ℝ)^4747 ≤ (16617356754283/50000000000000 : ℝ)^3723 := by
    have hnat : (84298883 : ℕ)^4747*50000000000000^3723 ≤ 16617356754283^3723*200000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84298883 200000000 16617356754283 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3881872687/10000000000 : ℝ)^4747 ≤ (14961609973153/50000000000000 : ℝ)^3723 := by
    have hnat : (3881872687 : ℕ)^4747*50000000000000^3723 ≤ 14961609973153^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3881872687 10000000000 14961609973153 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114243153/250000000 : ℝ)^4747 ≤ (7368413305441/20000000000000 : ℝ)^3723 := by
    have hnat : (114243153 : ℕ)^4747*20000000000000^3723 ≤ 7368413305441^3723*250000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114243153 250000000 7368413305441 20000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84298883/200000000 : ℝ), (3881872687/10000000000 : ℝ), (114243153/250000000 : ℝ)] ![(16617356754283/50000000000000 : ℝ), (14961609973153/50000000000000 : ℝ), (7368413305441/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84298883/200000000 : ℝ)|^4747 ≤ (16617356754283/50000000000000 : ℝ)^3723
        have hw : |(84298883/200000000 : ℝ)|=(84298883/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3881872687/10000000000 : ℝ)|^4747 ≤ (14961609973153/50000000000000 : ℝ)^3723
        have hw : |(3881872687/10000000000 : ℝ)|=(3881872687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(114243153/250000000 : ℝ)|^4747 ≤ (7368413305441/20000000000000 : ℝ)^3723
        have hw : |(114243153/250000000 : ℝ)|=(114243153/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s3_4 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1711807109/10000000000 : ℝ)*x 0 + (2591031349/5000000000 : ℝ)*x 1 + (2729439729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1711807109/10000000000 : ℝ)^4747 ≤ (10534619917411/100000000000000 : ℝ)^3723 := by
    have hnat : (1711807109 : ℕ)^4747*100000000000000^3723 ≤ 10534619917411^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1711807109 10000000000 10534619917411 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591031349/5000000000 : ℝ)^4747 ≤ (4324913997537/10000000000000 : ℝ)^3723 := by
    have hnat : (2591031349 : ℕ)^4747*10000000000000^3723 ≤ 4324913997537^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591031349 5000000000 4324913997537 10000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729439729/5000000000 : ℝ)^4747 ≤ (23108120043087/50000000000000 : ℝ)^3723 := by
    have hnat : (2729439729 : ℕ)^4747*50000000000000^3723 ≤ 23108120043087^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729439729 5000000000 23108120043087 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1711807109/10000000000 : ℝ), (2591031349/5000000000 : ℝ), (2729439729/5000000000 : ℝ)] ![(10534619917411/100000000000000 : ℝ), (4324913997537/10000000000000 : ℝ), (23108120043087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1711807109/10000000000 : ℝ)|^4747 ≤ (10534619917411/100000000000000 : ℝ)^3723
        have hw : |(-1711807109/10000000000 : ℝ)|=(1711807109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591031349/5000000000 : ℝ)|^4747 ≤ (4324913997537/10000000000000 : ℝ)^3723
        have hw : |(2591031349/5000000000 : ℝ)|=(2591031349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729439729/5000000000 : ℝ)|^4747 ≤ (23108120043087/50000000000000 : ℝ)^3723
        have hw : |(2729439729/5000000000 : ℝ)|=(2729439729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s3_5 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055911989/2000000000 : ℝ)*x 0 + (-394443279/2500000000 : ℝ)*x 1 + (2729439747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055911989/2000000000 : ℝ)^4747 ≤ (44289324902273/100000000000000 : ℝ)^3723 := by
    have hnat : (1055911989 : ℕ)^4747*100000000000000^3723 ≤ 44289324902273^3723*2000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055911989 2000000000 44289324902273 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (394443279/2500000000 : ℝ)^4747 ≤ (1186804325479/12500000000000 : ℝ)^3723 := by
    have hnat : (394443279 : ℕ)^4747*12500000000000^3723 ≤ 1186804325479^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394443279 2500000000 1186804325479 12500000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729439747/5000000000 : ℝ)^4747 ≤ (46216240474789/100000000000000 : ℝ)^3723 := by
    have hnat : (2729439747 : ℕ)^4747*100000000000000^3723 ≤ 46216240474789^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729439747 5000000000 46216240474789 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055911989/2000000000 : ℝ), (-394443279/2500000000 : ℝ), (2729439747/5000000000 : ℝ)] ![(44289324902273/100000000000000 : ℝ), (1186804325479/12500000000000 : ℝ), (46216240474789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055911989/2000000000 : ℝ)|^4747 ≤ (44289324902273/100000000000000 : ℝ)^3723
        have hw : |(1055911989/2000000000 : ℝ)|=(1055911989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-394443279/2500000000 : ℝ)|^4747 ≤ (1186804325479/12500000000000 : ℝ)^3723
        have hw : |(-394443279/2500000000 : ℝ)|=(394443279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729439747/5000000000 : ℝ)|^4747 ≤ (46216240474789/100000000000000 : ℝ)^3723
        have hw : |(2729439747/5000000000 : ℝ)|=(2729439747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s3_6 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055911993/2000000000 : ℝ)*x 0 + (341179967/625000000 : ℝ)*x 1 + (-1577773119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055911993/2000000000 : ℝ)^4747 ≤ (11072331279049/25000000000000 : ℝ)^3723 := by
    have hnat : (1055911993 : ℕ)^4747*25000000000000^3723 ≤ 11072331279049^3723*2000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055911993 2000000000 11072331279049 25000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341179967/625000000 : ℝ)^4747 ≤ (23108120118651/50000000000000 : ℝ)^3723 := by
    have hnat : (341179967 : ℕ)^4747*50000000000000^3723 ≤ 23108120118651^3723*625000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341179967 625000000 23108120118651 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577773119/10000000000 : ℝ)^4747 ≤ (189888692537/2000000000000 : ℝ)^3723 := by
    have hnat : (1577773119 : ℕ)^4747*2000000000000^3723 ≤ 189888692537^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577773119 10000000000 189888692537 2000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055911993/2000000000 : ℝ), (341179967/625000000 : ℝ), (-1577773119/10000000000 : ℝ)] ![(11072331279049/25000000000000 : ℝ), (23108120118651/50000000000000 : ℝ), (189888692537/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055911993/2000000000 : ℝ)|^4747 ≤ (11072331279049/25000000000000 : ℝ)^3723
        have hw : |(1055911993/2000000000 : ℝ)|=(1055911993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341179967/625000000 : ℝ)|^4747 ≤ (23108120118651/50000000000000 : ℝ)^3723
        have hw : |(341179967/625000000 : ℝ)|=(341179967/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1577773119/10000000000 : ℝ)|^4747 ≤ (189888692537/2000000000000 : ℝ)^3723
        have hw : |(-1577773119/10000000000 : ℝ)|=(1577773119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s3_7 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2107559771/5000000000 : ℝ)*x 0 + (1141149989/2500000000 : ℝ)*x 1 + (1943526457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107559771/5000000000 : ℝ)^4747 ≤ (6647295371757/20000000000000 : ℝ)^3723 := by
    have hnat : (2107559771 : ℕ)^4747*20000000000000^3723 ≤ 6647295371757^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107559771 5000000000 6647295371757 20000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141149989/2500000000 : ℝ)^4747 ≤ (7357875856669/20000000000000 : ℝ)^3723 := by
    have hnat : (1141149989 : ℕ)^4747*20000000000000^3723 ≤ 7357875856669^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141149989 2500000000 7357875856669 20000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1943526457/5000000000 : ℝ)^4747 ≤ (14987071925259/50000000000000 : ℝ)^3723 := by
    have hnat : (1943526457 : ℕ)^4747*50000000000000^3723 ≤ 14987071925259^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943526457 5000000000 14987071925259 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2107559771/5000000000 : ℝ), (1141149989/2500000000 : ℝ), (1943526457/5000000000 : ℝ)] ![(6647295371757/20000000000000 : ℝ), (7357875856669/20000000000000 : ℝ), (14987071925259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2107559771/5000000000 : ℝ)|^4747 ≤ (6647295371757/20000000000000 : ℝ)^3723
        have hw : |(2107559771/5000000000 : ℝ)|=(2107559771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1141149989/2500000000 : ℝ)|^4747 ≤ (7357875856669/20000000000000 : ℝ)^3723
        have hw : |(1141149989/2500000000 : ℝ)|=(1141149989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1943526457/5000000000 : ℝ)|^4747 ≤ (14987071925259/50000000000000 : ℝ)^3723
        have hw : |(1943526457/5000000000 : ℝ)|=(1943526457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1607_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16507/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10271/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10403/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (409/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16507/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10271/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16507/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10271/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16507/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10271/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16507/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10271/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16507/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10271/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16507/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10271/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10271/100000 : ℝ) ^ (4743/1024 : ℝ) ≤ (1321059332270497/50000000000000000000 : ℝ) := by
    have hpowers : (10271/100000 : ℝ)^4743 ≤ (1321059332270497/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10271 : ℕ)^4743*50000000000000000000^1024 ≤ 1321059332270497^1024*100000^4743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10271 100000 1321059332270497 50000000000000000000 4743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10271/100000 : ℝ)) (X := (1321059332270497/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16507/100000 : ℝ) ^ (4743/1024 : ℝ) ≤ (23788509306799167/100000000000000000000 : ℝ) := by
    have hpowers : (16507/100000 : ℝ)^4743 ≤ (23788509306799167/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16507 : ℕ)^4743*100000000000000000000^1024 ≤ 23788509306799167^1024*100000^4743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16507 100000 23788509306799167 100000000000000000000 4743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16507/100000 : ℝ)) (X := (23788509306799167/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001321059332270497/25000000000000000000 : ℝ) ≤ (10000114082794181/10000000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (25001321059332270497/25000000000000000000 : ℝ)^1024 ≤ (10000114082794181/10000000000000000 : ℝ)^4743 := by
      have hnat : (25001321059332270497 : ℕ)^1024*10000000000000000^4743 ≤ 10000114082794181^4743*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001321059332270497 25000000000000000000 10000114082794181 10000000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000114082794181/10000000000000000 : ℝ)) (X := (25001321059332270497/25000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026430627971340161/100000000000000000000 : ℝ) ≤ (5000285285251603/5000000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (100026430627971340161/100000000000000000000 : ℝ)^1024 ≤ (5000285285251603/5000000000000000 : ℝ)^4743 := by
      have hnat : (100026430627971340161 : ℕ)^1024*5000000000000000^4743 ≤ 5000285285251603^4743*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026430627971340161 100000000000000000000 5000285285251603 5000000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000285285251603/5000000000000000 : ℝ)) (X := (100026430627971340161/100000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023788509306799167/50000000000000000000 : ℝ) ≤ (10001027058212231/10000000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (50023788509306799167/50000000000000000000 : ℝ)^1024 ≤ (10001027058212231/10000000000000000 : ℝ)^4743 := by
      have hnat : (50023788509306799167 : ℕ)^1024*10000000000000000^4743 ≤ 10001027058212231^4743*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023788509306799167 50000000000000000000 10001027058212231 10000000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001027058212231/10000000000000000 : ℝ)) (X := (50023788509306799167/50000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1321059332270497/50000000000000000000 : ℝ) ≤ ((31175667124892860583/31180000000000000000 : ℝ)+2*(18259508361/24944000000000 : ℝ)*(10271/100000 : ℝ))^(4743/1024 : ℝ) := by
    rw [show (31175667124892860583/31180000000000000000 : ℝ)+2*(18259508361/24944000000000 : ℝ)*(10271/100000 : ℝ)=(10000114082794181/10000000000000000 : ℝ) by norm_num, show 1+2*(1321059332270497/50000000000000000000 : ℝ)=(25001321059332270497/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23788509306799167/100000000000000000000 : ℝ)+(1321059332270497/50000000000000000000 : ℝ) ≤ ((31175667124892860583/31180000000000000000 : ℝ)+(18259508361/24944000000000 : ℝ)*((16507/100000 : ℝ)+(10271/100000 : ℝ)))^(4743/1024 : ℝ) := by
    rw [show (31175667124892860583/31180000000000000000 : ℝ)+(18259508361/24944000000000 : ℝ)*((16507/100000 : ℝ)+(10271/100000 : ℝ))=(5000285285251603/5000000000000000 : ℝ) by norm_num, show 1+(23788509306799167/100000000000000000000 : ℝ)+(1321059332270497/50000000000000000000 : ℝ)=(100026430627971340161/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23788509306799167/100000000000000000000 : ℝ) ≤ ((31175667124892860583/31180000000000000000 : ℝ)+2*(18259508361/24944000000000 : ℝ)*(16507/100000 : ℝ))^(4743/1024 : ℝ) := by
    rw [show (31175667124892860583/31180000000000000000 : ℝ)+2*(18259508361/24944000000000 : ℝ)*(16507/100000 : ℝ)=(10001027058212231/10000000000000000 : ℝ) by norm_num, show 1+2*(23788509306799167/100000000000000000000 : ℝ)=(50023788509306799167/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31175667124892860583/31180000000000000000 : ℝ)*(X 1 0+X 2 0)+(18259508361/24944000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (10271/100000 : ℝ)) (hi := (16507/100000 : ℝ)) (c := (31175667124892860583/31180000000000000000 : ℝ)) (alpha := (18259508361/24944000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31175667124892860583/31180000000000000000 : ℝ)*(X 0 1+X 2 1)+(18259508361/24944000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (10271/100000 : ℝ)) (hi := (16507/100000 : ℝ)) (c := (31175667124892860583/31180000000000000000 : ℝ)) (alpha := (18259508361/24944000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31175667124892860583/31180000000000000000 : ℝ)*(X 0 2+X 1 2)+(18259508361/24944000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (10271/100000 : ℝ)) (hi := (16507/100000 : ℝ)) (c := (31175667124892860583/31180000000000000000 : ℝ)) (alpha := (18259508361/24944000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1711735483/10000000000 : ℝ)*X 0 0+(5460995901/10000000000 : ℝ)*X 0 1+(647496041/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133853851/250000000 : ℝ)*X 1 0+(-928342131/5000000000 : ℝ)*X 1 1+(5179968329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677077021/5000000000 : ℝ)*X 2 0+(647496041/1250000000 : ℝ)*X 2 1+(-1856684261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((84298883/200000000 : ℝ)*X 0 0+(3881872687/10000000000 : ℝ)*X 0 1+(114243153/250000000 : ℝ)*X 0 2+(84298883/200000000 : ℝ)*X 1 0+(3881872687/10000000000 : ℝ)*X 1 1+(114243153/250000000 : ℝ)*X 1 2+(84298883/200000000 : ℝ)*X 2 0+(3881872687/10000000000 : ℝ)*X 2 1+(114243153/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1711807109/10000000000 : ℝ)*X 0 0+(2591031349/5000000000 : ℝ)*X 0 1+(2729439729/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055911989/2000000000 : ℝ)*X 1 0+(-394443279/2500000000 : ℝ)*X 1 1+(2729439747/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055911993/2000000000 : ℝ)*X 2 0+(341179967/625000000 : ℝ)*X 2 1+(-1577773119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2107559771/5000000000 : ℝ)*X 0 0+(1141149989/2500000000 : ℝ)*X 0 1+(1943526457/5000000000 : ℝ)*X 0 2+(2107559771/5000000000 : ℝ)*X 1 0+(1141149989/2500000000 : ℝ)*X 1 1+(1943526457/5000000000 : ℝ)*X 1 2+(2107559771/5000000000 : ℝ)*X 2 0+(1141149989/2500000000 : ℝ)*X 2 1+(1943526457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4783684009565353610941519869/779500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101672097/10000000000000 : ℝ)*(base19) + (476726997/50000000000000 : ℝ)*(base23) + (540403/1562500000000 : ℝ)*(lower2) + (151599243/100000000000000 : ℝ)*(upper3) + (105260921/100000000000000 : ℝ)*(upper5) + (1253050703750627/50000000000000 : ℝ)*(major0) + (1253050703750627/50000000000000 : ℝ)*(major1) + (1253050703750627/50000000000000 : ℝ)*(major2) + (355838221478351/10000000000000 : ℝ)*(sp0) + (3558393345993799/100000000000000 : ℝ)*(sp1) + (142335736370431/4000000000000 : ℝ)*(sp2) + (290760573875867/20000000000000 : ℝ)*(sp3) + (12147931259/100000000000000 : ℝ)*(sp4) + (5378346327/100000000000000 : ℝ)*(sp7) + (726904123862831/50000000000000 : ℝ)*(f.failure) + (3558394362714769/100000000000000 : ℝ)*(f.sum) + (7575476224179/3118000000000000000000000000 : ℝ)*base66 + (14510460103847414459/1559000000000000000000000000000000 : ℝ)*base68 + (14345474144276414459/1559000000000000000000000000000000 : ℝ)*base70 + (10392059773652414459/1559000000000000000000000000000000 : ℝ)*base72 + (9639082418707/3118000000000000000000000000 : ℝ)*base74 + (23266918632947414459/1559000000000000000000000000000000 : ℝ)*base76 + (13459399429462414459/1559000000000000000000000000000000 : ℝ)*base78 + (16924205095419414459/1559000000000000000000000000000000 : ℝ)*base80 + (2164663505981/3118000000000000000000000000 : ℝ)*base81 + (192363/62500000000000000000 : ℝ)*base89 + (192363/62500000000000000000 : ℝ)*base91 + (192363/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2705157436626111906259464723/389750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (127319863/12500000000000 : ℝ)*(base19) + (114904821/10000000000000 : ℝ)*(base23) + (151546781/100000000000000 : ℝ)*(upper3) + (50608439/100000000000000 : ℝ)*(lower4) + (13108273/10000000000000 : ℝ)*(upper5) + (1272102355492527/50000000000000 : ℝ)*(major0) + (1272102355492527/50000000000000 : ℝ)*(major1) + (1272102355492527/50000000000000 : ℝ)*(major2) + (29041333/250000000000 : ℝ)*(sp1) + (6549558829/50000000000000 : ℝ)*(sp2) + (1806248465186531/50000000000000 : ℝ)*(sp4) + (1806242147640479/50000000000000 : ℝ)*(sp5) + (3612482682207193/100000000000000 : ℝ)*(sp6) + (1475912260238697/100000000000000 : ℝ)*(sp7) + (1475912260238697/100000000000000 : ℝ)*(f.failure) + (1806248465186531/50000000000000 : ℝ)*(f.sum) + (2889127499347/3118000000000000000000000000 : ℝ)*base65 + (11983029013153886759/1559000000000000000000000000000000 : ℝ)*base68 + (11874576938067886759/1559000000000000000000000000000000 : ℝ)*base70 + (11933505002237886759/1559000000000000000000000000000000 : ℝ)*base72 + (7627069470363/3118000000000000000000000000 : ℝ)*base73 + (7109552143771886759/1559000000000000000000000000000000 : ℝ)*base76 + (7661761706426886759/1559000000000000000000000000000000 : ℝ)*base78 + (2219871558850113241/1559000000000000000000000000000000 : ℝ)*base79 + (1473030624581/3118000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (350781/125000000000000000000 : ℝ)*base89 + (350781/125000000000000000000 : ℝ)*base91 + (350781/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1607_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16507/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10271/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10403/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (409/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1607_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1607_s4_0 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-855930397/5000000000 : ℝ)*x 0 + (218414803/400000000 : ℝ)*x 1 + (1036102177/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855930397/5000000000 : ℝ)^4747 ≤ (5267520586207/50000000000000 : ℝ)^3723 := by
    have hnat : (855930397 : ℕ)^4747*50000000000000^3723 ≤ 5267520586207^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855930397 5000000000 5267520586207 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218414803/400000000 : ℝ)^4747 ≤ (5779041462859/12500000000000 : ℝ)^3723 := by
    have hnat : (218414803 : ℕ)^4747*12500000000000^3723 ≤ 5779041462859^3723*400000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218414803 400000000 5779041462859 12500000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036102177/2000000000 : ℝ)^4747 ≤ (8646525421493/20000000000000 : ℝ)^3723 := by
    have hnat : (1036102177 : ℕ)^4747*20000000000000^3723 ≤ 8646525421493^3723*2000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036102177 2000000000 8646525421493 20000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-855930397/5000000000 : ℝ), (218414803/400000000 : ℝ), (1036102177/2000000000 : ℝ)] ![(5267520586207/50000000000000 : ℝ), (5779041462859/12500000000000 : ℝ), (8646525421493/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-855930397/5000000000 : ℝ)|^4747 ≤ (5267520586207/50000000000000 : ℝ)^3723
        have hw : |(-855930397/5000000000 : ℝ)|=(855930397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218414803/400000000 : ℝ)|^4747 ≤ (5779041462859/12500000000000 : ℝ)^3723
        have hw : |(218414803/400000000 : ℝ)|=(218414803/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036102177/2000000000 : ℝ)|^4747 ≤ (8646525421493/20000000000000 : ℝ)^3723
        have hw : |(1036102177/2000000000 : ℝ)|=(1036102177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s4_1 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676993407/5000000000 : ℝ)*x 0 + (-74247543/400000000 : ℝ)*x 1 + (518051087/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676993407/5000000000 : ℝ)^4747 ≤ (22543472035903/50000000000000 : ℝ)^3723 := by
    have hnat : (2676993407 : ℕ)^4747*50000000000000^3723 ≤ 22543472035903^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676993407 5000000000 22543472035903 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (74247543/400000000 : ℝ)^4747 ≤ (233608579481/2000000000000 : ℝ)^3723 := by
    have hnat : (74247543 : ℕ)^4747*2000000000000^3723 ≤ 233608579481^3723*400000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74247543 400000000 233608579481 2000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518051087/1000000000 : ℝ)^4747 ≤ (2702039184241/6250000000000 : ℝ)^3723 := by
    have hnat : (518051087 : ℕ)^4747*6250000000000^3723 ≤ 2702039184241^3723*1000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518051087 1000000000 2702039184241 6250000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676993407/5000000000 : ℝ), (-74247543/400000000 : ℝ), (518051087/1000000000 : ℝ)] ![(22543472035903/50000000000000 : ℝ), (233608579481/2000000000000 : ℝ), (2702039184241/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676993407/5000000000 : ℝ)|^4747 ≤ (22543472035903/50000000000000 : ℝ)^3723
        have hw : |(2676993407/5000000000 : ℝ)|=(2676993407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-74247543/400000000 : ℝ)|^4747 ≤ (233608579481/2000000000000 : ℝ)^3723
        have hw : |(-74247543/400000000 : ℝ)|=(74247543/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518051087/1000000000 : ℝ)|^4747 ≤ (2702039184241/6250000000000 : ℝ)^3723
        have hw : |(518051087/1000000000 : ℝ)|=(518051087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s4_2 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338496691/2500000000 : ℝ)*x 0 + (2590255473/5000000000 : ℝ)*x 1 + (-1856188539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338496691/2500000000 : ℝ)^4747 ≤ (5635867941867/12500000000000 : ℝ)^3723 := by
    have hnat : (1338496691 : ℕ)^4747*12500000000000^3723 ≤ 5635867941867^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338496691 2500000000 5635867941867 12500000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590255473/5000000000 : ℝ)^4747 ≤ (2161631387827/5000000000000 : ℝ)^3723 := by
    have hnat : (2590255473 : ℕ)^4747*5000000000000^3723 ≤ 2161631387827^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590255473 5000000000 2161631387827 5000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1856188539/10000000000 : ℝ)^4747 ≤ (2336085737041/20000000000000 : ℝ)^3723 := by
    have hnat : (1856188539 : ℕ)^4747*20000000000000^3723 ≤ 2336085737041^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856188539 10000000000 2336085737041 20000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338496691/2500000000 : ℝ), (2590255473/5000000000 : ℝ), (-1856188539/10000000000 : ℝ)] ![(5635867941867/12500000000000 : ℝ), (2161631387827/5000000000000 : ℝ), (2336085737041/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338496691/2500000000 : ℝ)|^4747 ≤ (5635867941867/12500000000000 : ℝ)^3723
        have hw : |(1338496691/2500000000 : ℝ)|=(1338496691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590255473/5000000000 : ℝ)|^4747 ≤ (2161631387827/5000000000000 : ℝ)^3723
        have hw : |(2590255473/5000000000 : ℝ)|=(2590255473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1856188539/10000000000 : ℝ)|^4747 ≤ (2336085737041/20000000000000 : ℝ)^3723
        have hw : |(-1856188539/10000000000 : ℝ)|=(1856188539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s4_3 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52687819/125000000 : ℝ)*x 0 + (3883293909/10000000000 : ℝ)*x 1 + (4568287547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52687819/125000000 : ℝ)^4747 ≤ (33235531581039/100000000000000 : ℝ)^3723 := by
    have hnat : (52687819 : ℕ)^4747*100000000000000^3723 ≤ 33235531581039^3723*125000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52687819 125000000 33235531581039 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3883293909/10000000000 : ℝ)^4747 ≤ (7484297330667/25000000000000 : ℝ)^3723 := by
    have hnat : (3883293909 : ℕ)^4747*25000000000000^3723 ≤ 7484297330667^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3883293909 10000000000 7484297330667 25000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4568287547/10000000000 : ℝ)^4747 ≤ (18413639541703/50000000000000 : ℝ)^3723 := by
    have hnat : (4568287547 : ℕ)^4747*50000000000000^3723 ≤ 18413639541703^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4568287547 10000000000 18413639541703 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52687819/125000000 : ℝ), (3883293909/10000000000 : ℝ), (4568287547/10000000000 : ℝ)] ![(33235531581039/100000000000000 : ℝ), (7484297330667/25000000000000 : ℝ), (18413639541703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52687819/125000000 : ℝ)|^4747 ≤ (33235531581039/100000000000000 : ℝ)^3723
        have hw : |(52687819/125000000 : ℝ)|=(52687819/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3883293909/10000000000 : ℝ)|^4747 ≤ (7484297330667/25000000000000 : ℝ)^3723
        have hw : |(3883293909/10000000000 : ℝ)|=(3883293909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4568287547/10000000000 : ℝ)|^4747 ≤ (18413639541703/50000000000000 : ℝ)^3723
        have hw : |(4568287547/10000000000 : ℝ)|=(4568287547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s4_4 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-427982883/2500000000 : ℝ)*x 0 + (2591293963/5000000000 : ℝ)*x 1 + (2729135617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427982883/2500000000 : ℝ)^4747 ≤ (105355962443/1000000000000 : ℝ)^3723 := by
    have hnat : (427982883 : ℕ)^4747*1000000000000^3723 ≤ 105355962443^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427982883 2500000000 105355962443 1000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591293963/5000000000 : ℝ)^4747 ≤ (43254729243339/100000000000000 : ℝ)^3723 := by
    have hnat : (2591293963 : ℕ)^4747*100000000000000^3723 ≤ 43254729243339^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591293963 5000000000 43254729243339 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729135617/5000000000 : ℝ)^4747 ≤ (46209674489507/100000000000000 : ℝ)^3723 := by
    have hnat : (2729135617 : ℕ)^4747*100000000000000^3723 ≤ 46209674489507^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729135617 5000000000 46209674489507 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427982883/2500000000 : ℝ), (2591293963/5000000000 : ℝ), (2729135617/5000000000 : ℝ)] ![(105355962443/1000000000000 : ℝ), (43254729243339/100000000000000 : ℝ), (46209674489507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427982883/2500000000 : ℝ)|^4747 ≤ (105355962443/1000000000000 : ℝ)^3723
        have hw : |(-427982883/2500000000 : ℝ)|=(427982883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591293963/5000000000 : ℝ)|^4747 ≤ (43254729243339/100000000000000 : ℝ)^3723
        have hw : |(2591293963/5000000000 : ℝ)|=(2591293963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729135617/5000000000 : ℝ)|^4747 ≤ (46209674489507/100000000000000 : ℝ)^3723
        have hw : |(2729135617/5000000000 : ℝ)|=(2729135617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s4_5 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639851917/5000000000 : ℝ)*x 0 + (-1578428247/10000000000 : ℝ)*x 1 + (5458271233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639851917/5000000000 : ℝ)^4747 ≤ (11072715991633/25000000000000 : ℝ)^3723 := by
    have hnat : (2639851917 : ℕ)^4747*25000000000000^3723 ≤ 11072715991633^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639851917 5000000000 11072715991633 25000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1578428247/10000000000 : ℝ)^4747 ≤ (2374865385947/25000000000000 : ℝ)^3723 := by
    have hnat : (1578428247 : ℕ)^4747*25000000000000^3723 ≤ 2374865385947^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1578428247 10000000000 2374865385947 25000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458271233/10000000000 : ℝ)^4747 ≤ (46209674478713/100000000000000 : ℝ)^3723 := by
    have hnat : (5458271233 : ℕ)^4747*100000000000000^3723 ≤ 46209674478713^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458271233 10000000000 46209674478713 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639851917/5000000000 : ℝ), (-1578428247/10000000000 : ℝ), (5458271233/10000000000 : ℝ)] ![(11072715991633/25000000000000 : ℝ), (2374865385947/25000000000000 : ℝ), (46209674478713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639851917/5000000000 : ℝ)|^4747 ≤ (11072715991633/25000000000000 : ℝ)^3723
        have hw : |(2639851917/5000000000 : ℝ)|=(2639851917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1578428247/10000000000 : ℝ)|^4747 ≤ (2374865385947/25000000000000 : ℝ)^3723
        have hw : |(-1578428247/10000000000 : ℝ)|=(1578428247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458271233/10000000000 : ℝ)|^4747 ≤ (46209674478713/100000000000000 : ℝ)^3723
        have hw : |(5458271233/10000000000 : ℝ)|=(5458271233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s4_6 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279703841/10000000000 : ℝ)*x 0 + (1364567807/2500000000 : ℝ)*x 1 + (-394607061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279703841/10000000000 : ℝ)^4747 ≤ (8858172808281/20000000000000 : ℝ)^3723 := by
    have hnat : (5279703841 : ℕ)^4747*20000000000000^3723 ≤ 8858172808281^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279703841 10000000000 8858172808281 20000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364567807/2500000000 : ℝ)^4747 ≤ (2310483721237/5000000000000 : ℝ)^3723 := by
    have hnat : (1364567807 : ℕ)^4747*5000000000000^3723 ≤ 2310483721237^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364567807 2500000000 2310483721237 5000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394607061/2500000000 : ℝ)^4747 ≤ (9499461520767/100000000000000 : ℝ)^3723 := by
    have hnat : (394607061 : ℕ)^4747*100000000000000^3723 ≤ 9499461520767^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394607061 2500000000 9499461520767 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279703841/10000000000 : ℝ), (1364567807/2500000000 : ℝ), (-394607061/2500000000 : ℝ)] ![(8858172808281/20000000000000 : ℝ), (2310483721237/5000000000000 : ℝ), (9499461520767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279703841/10000000000 : ℝ)|^4747 ≤ (8858172808281/20000000000000 : ℝ)^3723
        have hw : |(5279703841/10000000000 : ℝ)|=(5279703841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364567807/2500000000 : ℝ)|^4747 ≤ (2310483721237/5000000000000 : ℝ)^3723
        have hw : |(1364567807/2500000000 : ℝ)|=(1364567807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394607061/2500000000 : ℝ)|^4747 ≤ (9499461520767/100000000000000 : ℝ)^3723
        have hw : |(-394607061/2500000000 : ℝ)|=(394607061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s4_7 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4215198703/10000000000 : ℝ)*x 0 + (4563203741/10000000000 : ℝ)*x 1 + (3888431143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4215198703/10000000000 : ℝ)^4747 ≤ (33237272731607/100000000000000 : ℝ)^3723 := by
    have hnat : (4215198703 : ℕ)^4747*100000000000000^3723 ≤ 33237272731607^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215198703 10000000000 33237272731607 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4563203741/10000000000 : ℝ)^4747 ≤ (36775031660131/100000000000000 : ℝ)^3723 := by
    have hnat : (4563203741 : ℕ)^4747*100000000000000^3723 ≤ 36775031660131^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4563203741 10000000000 36775031660131 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3888431143/10000000000 : ℝ)^4747 ≤ (14993847795691/50000000000000 : ℝ)^3723 := by
    have hnat : (3888431143 : ℕ)^4747*50000000000000^3723 ≤ 14993847795691^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3888431143 10000000000 14993847795691 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4215198703/10000000000 : ℝ), (4563203741/10000000000 : ℝ), (3888431143/10000000000 : ℝ)] ![(33237272731607/100000000000000 : ℝ), (36775031660131/100000000000000 : ℝ), (14993847795691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4215198703/10000000000 : ℝ)|^4747 ≤ (33237272731607/100000000000000 : ℝ)^3723
        have hw : |(4215198703/10000000000 : ℝ)|=(4215198703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4563203741/10000000000 : ℝ)|^4747 ≤ (36775031660131/100000000000000 : ℝ)^3723
        have hw : |(4563203741/10000000000 : ℝ)|=(4563203741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3888431143/10000000000 : ℝ)|^4747 ≤ (14993847795691/50000000000000 : ℝ)^3723
        have hw : |(3888431143/10000000000 : ℝ)|=(3888431143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1607_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (409/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2083/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16347/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (409/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10403/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (409/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10403/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (409/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10403/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (409/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10403/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (409/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10403/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (409/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10403/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10403/100000 : ℝ) ^ (4743/1024 : ℝ) ≤ (2803108288802921/100000000000000000000 : ℝ) := by
    have hpowers : (10403/100000 : ℝ)^4743 ≤ (2803108288802921/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10403 : ℕ)^4743*100000000000000000000^1024 ≤ 2803108288802921^1024*100000^4743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10403 100000 2803108288802921 100000000000000000000 4743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10403/100000 : ℝ)) (X := (2803108288802921/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (409/2500 : ℝ) ^ (4743/1024 : ℝ) ≤ (22823026325393249/100000000000000000000 : ℝ) := by
    have hpowers : (409/2500 : ℝ)^4743 ≤ (22823026325393249/100000000000000000000 : ℝ)^1024 := by
      have hnat : (409 : ℕ)^4743*100000000000000000000^1024 ≤ 22823026325393249^1024*2500^4743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        409 2500 22823026325393249 100000000000000000000 4743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (409/2500 : ℝ)) (X := (22823026325393249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002803108288802921/50000000000000000000 : ℝ) ≤ (625007564621023/625000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (50002803108288802921/50000000000000000000 : ℝ)^1024 ≤ (625007564621023/625000000000000 : ℝ)^4743 := by
      have hnat : (50002803108288802921 : ℕ)^1024*625000000000000^4743 ≤ 625007564621023^4743*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002803108288802921 50000000000000000000 625007564621023 625000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625007564621023/625000000000000 : ℝ)) (X := (50002803108288802921/50000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002562613461419617/10000000000000000000 : ℝ) ≤ (10000553205267959/10000000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (10002562613461419617/10000000000000000000 : ℝ)^1024 ≤ (10000553205267959/10000000000000000 : ℝ)^4743 := by
      have hnat : (10002562613461419617 : ℕ)^1024*10000000000000000^4743 ≤ 10000553205267959^4743*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002562613461419617 10000000000000000000 10000553205267959 10000000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000553205267959/10000000000000000 : ℝ)) (X := (10002562613461419617/10000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022823026325393249/50000000000000000000 : ℝ) ≤ (200019707531991/200000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (50022823026325393249/50000000000000000000 : ℝ)^1024 ≤ (200019707531991/200000000000000 : ℝ)^4743 := by
      have hnat : (50022823026325393249 : ℕ)^1024*200000000000000^4743 ≤ 200019707531991^4743*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022823026325393249 50000000000000000000 200019707531991 200000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200019707531991/200000000000000 : ℝ)) (X := (50022823026325393249/50000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2803108288802921/100000000000000000000 : ℝ) ≤ ((5956172924243386183/5957000000000000000 : ℝ)+2*(432171331591/595700000000000 : ℝ)*(10403/100000 : ℝ))^(4743/1024 : ℝ) := by
    rw [show (5956172924243386183/5957000000000000000 : ℝ)+2*(432171331591/595700000000000 : ℝ)*(10403/100000 : ℝ)=(625007564621023/625000000000000 : ℝ) by norm_num, show 1+2*(2803108288802921/100000000000000000000 : ℝ)=(50002803108288802921/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22823026325393249/100000000000000000000 : ℝ)+(2803108288802921/100000000000000000000 : ℝ) ≤ ((5956172924243386183/5957000000000000000 : ℝ)+(432171331591/595700000000000 : ℝ)*((409/2500 : ℝ)+(10403/100000 : ℝ)))^(4743/1024 : ℝ) := by
    rw [show (5956172924243386183/5957000000000000000 : ℝ)+(432171331591/595700000000000 : ℝ)*((409/2500 : ℝ)+(10403/100000 : ℝ))=(10000553205267959/10000000000000000 : ℝ) by norm_num, show 1+(22823026325393249/100000000000000000000 : ℝ)+(2803108288802921/100000000000000000000 : ℝ)=(10002562613461419617/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22823026325393249/100000000000000000000 : ℝ) ≤ ((5956172924243386183/5957000000000000000 : ℝ)+2*(432171331591/595700000000000 : ℝ)*(409/2500 : ℝ))^(4743/1024 : ℝ) := by
    rw [show (5956172924243386183/5957000000000000000 : ℝ)+2*(432171331591/595700000000000 : ℝ)*(409/2500 : ℝ)=(200019707531991/200000000000000 : ℝ) by norm_num, show 1+2*(22823026325393249/100000000000000000000 : ℝ)=(50022823026325393249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5956172924243386183/5957000000000000000 : ℝ)*(X 1 0+X 2 0)+(432171331591/595700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (10403/100000 : ℝ)) (hi := (409/2500 : ℝ)) (c := (5956172924243386183/5957000000000000000 : ℝ)) (alpha := (432171331591/595700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5956172924243386183/5957000000000000000 : ℝ)*(X 0 1+X 2 1)+(432171331591/595700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (10403/100000 : ℝ)) (hi := (409/2500 : ℝ)) (c := (5956172924243386183/5957000000000000000 : ℝ)) (alpha := (432171331591/595700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5956172924243386183/5957000000000000000 : ℝ)*(X 0 2+X 1 2)+(432171331591/595700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (10403/100000 : ℝ)) (hi := (409/2500 : ℝ)) (c := (5956172924243386183/5957000000000000000 : ℝ)) (alpha := (432171331591/595700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-855930397/5000000000 : ℝ)*X 0 0+(218414803/400000000 : ℝ)*X 0 1+(1036102177/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676993407/5000000000 : ℝ)*X 1 0+(-74247543/400000000 : ℝ)*X 1 1+(518051087/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338496691/2500000000 : ℝ)*X 2 0+(2590255473/5000000000 : ℝ)*X 2 1+(-1856188539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((52687819/125000000 : ℝ)*X 0 0+(3883293909/10000000000 : ℝ)*X 0 1+(4568287547/10000000000 : ℝ)*X 0 2+(52687819/125000000 : ℝ)*X 1 0+(3883293909/10000000000 : ℝ)*X 1 1+(4568287547/10000000000 : ℝ)*X 1 2+(52687819/125000000 : ℝ)*X 2 0+(3883293909/10000000000 : ℝ)*X 2 1+(4568287547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-427982883/2500000000 : ℝ)*X 0 0+(2591293963/5000000000 : ℝ)*X 0 1+(2729135617/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639851917/5000000000 : ℝ)*X 1 0+(-1578428247/10000000000 : ℝ)*X 1 1+(5458271233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5279703841/10000000000 : ℝ)*X 2 0+(1364567807/2500000000 : ℝ)*X 2 1+(-394607061/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4215198703/10000000000 : ℝ)*X 0 0+(4563203741/10000000000 : ℝ)*X 0 1+(3888431143/10000000000 : ℝ)*X 0 2+(4215198703/10000000000 : ℝ)*X 1 0+(4563203741/10000000000 : ℝ)*X 1 1+(3888431143/10000000000 : ℝ)*X 1 2+(4215198703/10000000000 : ℝ)*X 2 0+(4563203741/10000000000 : ℝ)*X 2 1+(3888431143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57270661111538406474753009/21275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (249388073/50000000000000 : ℝ)*(base19) + (447328529/100000000000000 : ℝ)*(base23) + (9678799/100000000000000 : ℝ)*(lower2) + (14691057/25000000000000 : ℝ)*(upper3) + (16688419/25000000000000 : ℝ)*(upper5) + (1258277662604071/50000000000000 : ℝ)*(major0) + (1258277662604071/50000000000000 : ℝ)*(major1) + (1258277662604071/50000000000000 : ℝ)*(major2) + (71464631420199/2000000000000 : ℝ)*(sp0) + (446654677251411/12500000000000 : ℝ)*(sp1) + (714647493891781/20000000000000 : ℝ)*(sp2) + (1459870123901677/100000000000000 : ℝ)*(sp3) + (1586444371/25000000000000 : ℝ)*(sp4) + (2519996393/100000000000000 : ℝ)*(sp7) + (145987264389807/10000000000000 : ℝ)*(f.failure) + (1786618958393717/50000000000000 : ℝ)*(f.sum) + (117445721766913/29785000000000000000000000000 : ℝ)*base66 + (2257395190236560993/297850000000000000000000000000000 : ℝ)*base67 + (4511616775277160993/297850000000000000000000000000000 : ℝ)*base69 + (2642772668715210993/297850000000000000000000000000000 : ℝ)*base71 + (1268663272553/7446250000000000000000000000 : ℝ)*base73 + (5534344453118260993/297850000000000000000000000000000 : ℝ)*base75 + (2774786642839410993/297850000000000000000000000000000 : ℝ)*base77 + (5271229226282960993/297850000000000000000000000000000 : ℝ)*base79 + (81281460474367/29785000000000000000000000000 : ℝ)*base81 + (151189/12500000000000000000 : ℝ)*base90 + (151189/12500000000000000000 : ℝ)*base92 + (151189/12500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (544821794960694521943409581/74462500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (562011841/50000000000000 : ℝ)*(base19) + (611471237/50000000000000 : ℝ)*(base23) + (357154173/100000000000000 : ℝ)*(lower1) + (956151/625000000000 : ℝ)*(upper3) + (42220217/100000000000000 : ℝ)*(lower4) + (38121041/25000000000000 : ℝ)*(upper5) + (1277328142587869/50000000000000 : ℝ)*(major0) + (1277328142587869/50000000000000 : ℝ)*(major1) + (1277328142587869/50000000000000 : ℝ)*(major2) + (1005190799/100000000000000 : ℝ)*(sp2) + (725467405908159/20000000000000 : ℝ)*(sp4) + (453416988189639/12500000000000 : ℝ)*(sp5) + (1813667400703761/50000000000000 : ℝ)*(sp6) + (370493824229939/25000000000000 : ℝ)*(sp7) + (370493824229939/25000000000000 : ℝ)*(f.failure) + (725467405908159/20000000000000 : ℝ)*(f.sum) + (69402341283661/14892500000000000000000000000 : ℝ)*base66 + (7765700067939295973/297850000000000000000000000000000 : ℝ)*base68 + (1848613091429495973/297850000000000000000000000000000 : ℝ)*base70 + (31118696210407204027/297850000000000000000000000000000 : ℝ)*base71 + (79647130373231/14892500000000000000000000000 : ℝ)*base74 + (7460359687887595973/297850000000000000000000000000000 : ℝ)*base76 + (2023451270178295973/297850000000000000000000000000000 : ℝ)*base78 + (1445895446284295973/297850000000000000000000000000000 : ℝ)*base80 + (40917157041143/29785000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (223847/31250000000000000000 : ℝ)*base89 + (223847/31250000000000000000 : ℝ)*base91 + (223847/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1607_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (409/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2083/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16347/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1607_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1607_s5_0 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1711871283/10000000000 : ℝ)*x 0 + (2730157847/5000000000 : ℝ)*x 1 + (1295139581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1711871283/10000000000 : ℝ)^4747 ≤ (5267561738917/50000000000000 : ℝ)^3723 := by
    have hnat : (1711871283 : ℕ)^4747*50000000000000^3723 ≤ 5267561738917^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1711871283 10000000000 5267561738917 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730157847/5000000000 : ℝ)^4747 ≤ (46231744623921/100000000000000 : ℝ)^3723 := by
    have hnat : (2730157847 : ℕ)^4747*100000000000000^3723 ≤ 46231744623921^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730157847 5000000000 46231744623921 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295139581/2500000000 : ℝ)^4747 ≤ (21616565943247/50000000000000 : ℝ)^3723 := by
    have hnat : (1295139581 : ℕ)^4747*50000000000000^3723 ≤ 21616565943247^3723*2500000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295139581 2500000000 21616565943247 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1711871283/10000000000 : ℝ), (2730157847/5000000000 : ℝ), (1295139581/2500000000 : ℝ)] ![(5267561738917/50000000000000 : ℝ), (46231744623921/100000000000000 : ℝ), (21616565943247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1711871283/10000000000 : ℝ)|^4747 ≤ (5267561738917/50000000000000 : ℝ)^3723
        have hw : |(-1711871283/10000000000 : ℝ)|=(1711871283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730157847/5000000000 : ℝ)|^4747 ≤ (46231744623921/100000000000000 : ℝ)^3723
        have hw : |(2730157847/5000000000 : ℝ)|=(2730157847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295139581/2500000000 : ℝ)|^4747 ≤ (21616565943247/50000000000000 : ℝ)^3723
        have hw : |(1295139581/2500000000 : ℝ)|=(1295139581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s5_1 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676986177/5000000000 : ℝ)*x 0 + (-928072487/5000000000 : ℝ)*x 1 + (2590279169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676986177/5000000000 : ℝ)^4747 ≤ (22543394404429/50000000000000 : ℝ)^3723 := by
    have hnat : (2676986177 : ℕ)^4747*50000000000000^3723 ≤ 22543394404429^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676986177 5000000000 22543394404429 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (928072487/5000000000 : ℝ)^4747 ≤ (11680079143333/100000000000000 : ℝ)^3723 := by
    have hnat : (928072487 : ℕ)^4747*100000000000000^3723 ≤ 11680079143333^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928072487 5000000000 11680079143333 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590279169/5000000000 : ℝ)^4747 ≤ (43233132035463/100000000000000 : ℝ)^3723 := by
    have hnat : (2590279169 : ℕ)^4747*100000000000000^3723 ≤ 43233132035463^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590279169 5000000000 43233132035463 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676986177/5000000000 : ℝ), (-928072487/5000000000 : ℝ), (2590279169/5000000000 : ℝ)] ![(22543394404429/50000000000000 : ℝ), (11680079143333/100000000000000 : ℝ), (43233132035463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676986177/5000000000 : ℝ)|^4747 ≤ (22543394404429/50000000000000 : ℝ)^3723
        have hw : |(2676986177/5000000000 : ℝ)|=(2676986177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-928072487/5000000000 : ℝ)|^4747 ≤ (11680079143333/100000000000000 : ℝ)^3723
        have hw : |(-928072487/5000000000 : ℝ)|=(928072487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590279169/5000000000 : ℝ)|^4747 ≤ (43233132035463/100000000000000 : ℝ)^3723
        have hw : |(2590279169/5000000000 : ℝ)|=(2590279169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s5_2 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676986173/5000000000 : ℝ)*x 0 + (5180558349/10000000000 : ℝ)*x 1 + (-185614497/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676986173/5000000000 : ℝ)^4747 ≤ (22543394361479/50000000000000 : ℝ)^3723 := by
    have hnat : (2676986173 : ℕ)^4747*50000000000000^3723 ≤ 22543394361479^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676986173 5000000000 22543394361479 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180558349/10000000000 : ℝ)^4747 ≤ (43233132152509/100000000000000 : ℝ)^3723 := by
    have hnat : (5180558349 : ℕ)^4747*100000000000000^3723 ≤ 43233132152509^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180558349 10000000000 43233132152509 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (185614497/1000000000 : ℝ)^4747 ≤ (11680079111239/100000000000000 : ℝ)^3723 := by
    have hnat : (185614497 : ℕ)^4747*100000000000000^3723 ≤ 11680079111239^3723*1000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185614497 1000000000 11680079111239 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676986173/5000000000 : ℝ), (5180558349/10000000000 : ℝ), (-185614497/1000000000 : ℝ)] ![(22543394361479/50000000000000 : ℝ), (43233132152509/100000000000000 : ℝ), (11680079111239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676986173/5000000000 : ℝ)|^4747 ≤ (22543394361479/50000000000000 : ℝ)^3723
        have hw : |(2676986173/5000000000 : ℝ)|=(2676986173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180558349/10000000000 : ℝ)|^4747 ≤ (43233132152509/100000000000000 : ℝ)^3723
        have hw : |(5180558349/10000000000 : ℝ)|=(5180558349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-185614497/1000000000 : ℝ)|^4747 ≤ (11680079111239/100000000000000 : ℝ)^3723
        have hw : |(-185614497/1000000000 : ℝ)|=(185614497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s5_3 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4215032571/10000000000 : ℝ)*x 0 + (485427219/1250000000 : ℝ)*x 1 + (2284081109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4215032571/10000000000 : ℝ)^4747 ≤ (33235602470133/100000000000000 : ℝ)^3723 := by
    have hnat : (4215032571 : ℕ)^4747*100000000000000^3723 ≤ 33235602470133^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215032571 10000000000 33235602470133 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (485427219/1250000000 : ℝ)^4747 ≤ (14969203329139/50000000000000 : ℝ)^3723 := by
    have hnat : (485427219 : ℕ)^4747*50000000000000^3723 ≤ 14969203329139^3723*1250000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485427219 1250000000 14969203329139 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2284081109/5000000000 : ℝ)^4747 ≤ (184129954283/500000000000 : ℝ)^3723 := by
    have hnat : (2284081109 : ℕ)^4747*500000000000^3723 ≤ 184129954283^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284081109 5000000000 184129954283 500000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4215032571/10000000000 : ℝ), (485427219/1250000000 : ℝ), (2284081109/5000000000 : ℝ)] ![(33235602470133/100000000000000 : ℝ), (14969203329139/50000000000000 : ℝ), (184129954283/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4215032571/10000000000 : ℝ)|^4747 ≤ (33235602470133/100000000000000 : ℝ)^3723
        have hw : |(4215032571/10000000000 : ℝ)|=(4215032571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(485427219/1250000000 : ℝ)|^4747 ≤ (14969203329139/50000000000000 : ℝ)^3723
        have hw : |(485427219/1250000000 : ℝ)|=(485427219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2284081109/5000000000 : ℝ)|^4747 ≤ (184129954283/500000000000 : ℝ)^3723
        have hw : |(2284081109/5000000000 : ℝ)|=(2284081109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s5_4 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-342388399/2000000000 : ℝ)*x 0 + (5182633769/10000000000 : ℝ)*x 1 + (1091643687/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (342388399/2000000000 : ℝ)^4747 ≤ (2633919586659/25000000000000 : ℝ)^3723 := by
    have hnat : (342388399 : ℕ)^4747*25000000000000^3723 ≤ 2633919586659^3723*2000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342388399 2000000000 2633919586659 25000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182633769/10000000000 : ℝ)^4747 ≤ (10813804273437/25000000000000 : ℝ)^3723 := by
    have hnat : (5182633769 : ℕ)^4747*25000000000000^3723 ≤ 10813804273437^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182633769 10000000000 10813804273437 25000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091643687/2000000000 : ℝ)^4747 ≤ (23104552274771/50000000000000 : ℝ)^3723 := by
    have hnat : (1091643687 : ℕ)^4747*50000000000000^3723 ≤ 23104552274771^3723*2000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091643687 2000000000 23104552274771 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-342388399/2000000000 : ℝ), (5182633769/10000000000 : ℝ), (1091643687/2000000000 : ℝ)] ![(2633919586659/25000000000000 : ℝ), (10813804273437/25000000000000 : ℝ), (23104552274771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-342388399/2000000000 : ℝ)|^4747 ≤ (2633919586659/25000000000000 : ℝ)^3723
        have hw : |(-342388399/2000000000 : ℝ)|=(342388399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182633769/10000000000 : ℝ)|^4747 ≤ (10813804273437/25000000000000 : ℝ)^3723
        have hw : |(5182633769/10000000000 : ℝ)|=(5182633769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091643687/2000000000 : ℝ)|^4747 ≤ (23104552274771/50000000000000 : ℝ)^3723
        have hw : |(1091643687/2000000000 : ℝ)|=(1091643687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s5_5 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211188661/400000000 : ℝ)*x 0 + (-19731061/125000000 : ℝ)*x 1 + (2729109199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211188661/400000000 : ℝ)^4747 ≤ (692046870507/1562500000000 : ℝ)^3723 := by
    have hnat : (211188661 : ℕ)^4747*1562500000000^3723 ≤ 692046870507^3723*400000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211188661 400000000 692046870507 1562500000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19731061/125000000 : ℝ)^4747 ≤ (1899979225221/20000000000000 : ℝ)^3723 := by
    have hnat : (19731061 : ℕ)^4747*20000000000000^3723 ≤ 1899979225221^3723*125000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19731061 125000000 1899979225221 20000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729109199/5000000000 : ℝ)^4747 ≤ (23104552075073/50000000000000 : ℝ)^3723 := by
    have hnat : (2729109199 : ℕ)^4747*50000000000000^3723 ≤ 23104552075073^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729109199 5000000000 23104552075073 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211188661/400000000 : ℝ), (-19731061/125000000 : ℝ), (2729109199/5000000000 : ℝ)] ![(692046870507/1562500000000 : ℝ), (1899979225221/20000000000000 : ℝ), (23104552075073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211188661/400000000 : ℝ)|^4747 ≤ (692046870507/1562500000000 : ℝ)^3723
        have hw : |(211188661/400000000 : ℝ)|=(211188661/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19731061/125000000 : ℝ)|^4747 ≤ (1899979225221/20000000000000 : ℝ)^3723
        have hw : |(-19731061/125000000 : ℝ)|=(19731061/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729109199/5000000000 : ℝ)|^4747 ≤ (23104552075073/50000000000000 : ℝ)^3723
        have hw : |(2729109199/5000000000 : ℝ)|=(2729109199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s5_6 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055943331/2000000000 : ℝ)*x 0 + (5458218303/10000000000 : ℝ)*x 1 + (-1578484833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055943331/2000000000 : ℝ)^4747 ≤ (44291001102959/100000000000000 : ℝ)^3723 := by
    have hnat : (1055943331 : ℕ)^4747*100000000000000^3723 ≤ 44291001102959^3723*2000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055943331 2000000000 44291001102959 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458218303/10000000000 : ℝ)^4747 ≤ (46209103124667/100000000000000 : ℝ)^3723 := by
    have hnat : (5458218303 : ℕ)^4747*100000000000000^3723 ≤ 46209103124667^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458218303 10000000000 46209103124667 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1578484833/10000000000 : ℝ)^4747 ≤ (9499895765441/100000000000000 : ℝ)^3723 := by
    have hnat : (1578484833 : ℕ)^4747*100000000000000^3723 ≤ 9499895765441^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1578484833 10000000000 9499895765441 100000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055943331/2000000000 : ℝ), (5458218303/10000000000 : ℝ), (-1578484833/10000000000 : ℝ)] ![(44291001102959/100000000000000 : ℝ), (46209103124667/100000000000000 : ℝ), (9499895765441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055943331/2000000000 : ℝ)|^4747 ≤ (44291001102959/100000000000000 : ℝ)^3723
        have hw : |(1055943331/2000000000 : ℝ)|=(1055943331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458218303/10000000000 : ℝ)|^4747 ≤ (46209103124667/100000000000000 : ℝ)^3723
        have hw : |(5458218303/10000000000 : ℝ)|=(5458218303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1578484833/10000000000 : ℝ)|^4747 ≤ (9499895765441/100000000000000 : ℝ)^3723
        have hw : |(-1578484833/10000000000 : ℝ)|=(1578484833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1607_s5_7 (p : ℝ) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4215205783/10000000000 : ℝ)*x 0 + (91261637/200000000 : ℝ)*x 1 + (1944275639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4215205783/10000000000 : ℝ)^4747 ≤ (16618671956533/50000000000000 : ℝ)^3723 := by
    have hnat : (4215205783 : ℕ)^4747*50000000000000^3723 ≤ 16618671956533^3723*10000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215205783 10000000000 16618671956533 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91261637/200000000 : ℝ)^4747 ≤ (1470951166209/4000000000000 : ℝ)^3723 := by
    have hnat : (91261637 : ℕ)^4747*4000000000000^3723 ≤ 1470951166209^3723*200000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91261637 200000000 1470951166209 4000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1944275639/5000000000 : ℝ)^4747 ≤ (14994438453947/50000000000000 : ℝ)^3723 := by
    have hnat : (1944275639 : ℕ)^4747*50000000000000^3723 ≤ 14994438453947^3723*5000000000^4747 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944275639 5000000000 14994438453947 50000000000000 4747 3723 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4747/1024 : ℝ)) 4747 3723 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4215205783/10000000000 : ℝ), (91261637/200000000 : ℝ), (1944275639/5000000000 : ℝ)] ![(16618671956533/50000000000000 : ℝ), (1470951166209/4000000000000 : ℝ), (14994438453947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4215205783/10000000000 : ℝ)|^4747 ≤ (16618671956533/50000000000000 : ℝ)^3723
        have hw : |(4215205783/10000000000 : ℝ)|=(4215205783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(91261637/200000000 : ℝ)|^4747 ≤ (1470951166209/4000000000000 : ℝ)^3723
        have hw : |(91261637/200000000 : ℝ)|=(91261637/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1944275639/5000000000 : ℝ)|^4747 ≤ (14994438453947/50000000000000 : ℝ)^3723
        have hw : |(1944275639/5000000000 : ℝ)|=(1944275639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1607_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16347/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2083/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (651/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8173/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16347/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2083/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16347/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2083/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16347/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2083/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16347/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2083/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16347/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2083/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16347/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2083/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2083/20000 : ℝ) ^ (4743/1024 : ℝ) ≤ (2818116376863329/100000000000000000000 : ℝ) := by
    have hpowers : (2083/20000 : ℝ)^4743 ≤ (2818116376863329/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2083 : ℕ)^4743*100000000000000000000^1024 ≤ 2818116376863329^1024*20000^4743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2083 20000 2818116376863329 100000000000000000000 4743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2083/20000 : ℝ)) (X := (2818116376863329/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16347/100000 : ℝ) ^ (4743/1024 : ℝ) ≤ (22739146066056371/100000000000000000000 : ℝ) := by
    have hpowers : (16347/100000 : ℝ)^4743 ≤ (22739146066056371/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16347 : ℕ)^4743*100000000000000000000^1024 ≤ 22739146066056371^1024*100000^4743 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16347 100000 22739146066056371 100000000000000000000 4743 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16347/100000 : ℝ)) (X := (22739146066056371/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002818116376863329/50000000000000000000 : ℝ) ≤ (10000121681948379/10000000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (50002818116376863329/50000000000000000000 : ℝ)^1024 ≤ (10000121681948379/10000000000000000 : ℝ)^4743 := by
      have hnat : (50002818116376863329 : ℕ)^1024*10000000000000000^4743 ≤ 10000121681948379^4743*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002818116376863329 50000000000000000000 10000121681948379 10000000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000121681948379/10000000000000000 : ℝ)) (X := (50002818116376863329/50000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1000255572624429197/1000000000000000000 : ℝ) ≤ (5000275859317991/5000000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (1000255572624429197/1000000000000000000 : ℝ)^1024 ≤ (5000275859317991/5000000000000000 : ℝ)^4743 := by
      have hnat : (1000255572624429197 : ℕ)^1024*5000000000000000^4743 ≤ 5000275859317991^4743*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000255572624429197 1000000000000000000 5000275859317991 5000000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000275859317991/5000000000000000 : ℝ)) (X := (1000255572624429197/1000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022739146066056371/50000000000000000000 : ℝ) ≤ (2000196351064717/2000000000000000 : ℝ) ^ (4743/1024 : ℝ) := by
    have hpowers : (50022739146066056371/50000000000000000000 : ℝ)^1024 ≤ (2000196351064717/2000000000000000 : ℝ)^4743 := by
      have hnat : (50022739146066056371 : ℕ)^1024*2000000000000000^4743 ≤ 2000196351064717^4743*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022739146066056371 50000000000000000000 2000196351064717 2000000000000000 1024 4743 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000196351064717/2000000000000000 : ℝ)) (X := (50022739146066056371/50000000000000000000 : ℝ)) (by norm_num) 4743 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2818116376863329/100000000000000000000 : ℝ) ≤ ((29655882076557506869/29660000000000000000 : ℝ)+2*(430036687603/593200000000000 : ℝ)*(2083/20000 : ℝ))^(4743/1024 : ℝ) := by
    rw [show (29655882076557506869/29660000000000000000 : ℝ)+2*(430036687603/593200000000000 : ℝ)*(2083/20000 : ℝ)=(10000121681948379/10000000000000000 : ℝ) by norm_num, show 1+2*(2818116376863329/100000000000000000000 : ℝ)=(50002818116376863329/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22739146066056371/100000000000000000000 : ℝ)+(2818116376863329/100000000000000000000 : ℝ) ≤ ((29655882076557506869/29660000000000000000 : ℝ)+(430036687603/593200000000000 : ℝ)*((16347/100000 : ℝ)+(2083/20000 : ℝ)))^(4743/1024 : ℝ) := by
    rw [show (29655882076557506869/29660000000000000000 : ℝ)+(430036687603/593200000000000 : ℝ)*((16347/100000 : ℝ)+(2083/20000 : ℝ))=(5000275859317991/5000000000000000 : ℝ) by norm_num, show 1+(22739146066056371/100000000000000000000 : ℝ)+(2818116376863329/100000000000000000000 : ℝ)=(1000255572624429197/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22739146066056371/100000000000000000000 : ℝ) ≤ ((29655882076557506869/29660000000000000000 : ℝ)+2*(430036687603/593200000000000 : ℝ)*(16347/100000 : ℝ))^(4743/1024 : ℝ) := by
    rw [show (29655882076557506869/29660000000000000000 : ℝ)+2*(430036687603/593200000000000 : ℝ)*(16347/100000 : ℝ)=(2000196351064717/2000000000000000 : ℝ) by norm_num, show 1+2*(22739146066056371/100000000000000000000 : ℝ)=(50022739146066056371/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29655882076557506869/29660000000000000000 : ℝ)*(X 1 0+X 2 0)+(430036687603/593200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (2083/20000 : ℝ)) (hi := (16347/100000 : ℝ)) (c := (29655882076557506869/29660000000000000000 : ℝ)) (alpha := (430036687603/593200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29655882076557506869/29660000000000000000 : ℝ)*(X 0 1+X 2 1)+(430036687603/593200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (2083/20000 : ℝ)) (hi := (16347/100000 : ℝ)) (c := (29655882076557506869/29660000000000000000 : ℝ)) (alpha := (430036687603/593200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29655882076557506869/29660000000000000000 : ℝ)*(X 0 2+X 1 2)+(430036687603/593200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4743/1024 : ℝ)) (lo := (2083/20000 : ℝ)) (hi := (16347/100000 : ℝ)) (c := (29655882076557506869/29660000000000000000 : ℝ)) (alpha := (430036687603/593200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1711871283/10000000000 : ℝ)*X 0 0+(2730157847/5000000000 : ℝ)*X 0 1+(1295139581/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676986177/5000000000 : ℝ)*X 1 0+(-928072487/5000000000 : ℝ)*X 1 1+(2590279169/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676986173/5000000000 : ℝ)*X 2 0+(5180558349/10000000000 : ℝ)*X 2 1+(-185614497/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4215032571/10000000000 : ℝ)*X 0 0+(485427219/1250000000 : ℝ)*X 0 1+(2284081109/5000000000 : ℝ)*X 0 2+(4215032571/10000000000 : ℝ)*X 1 0+(485427219/1250000000 : ℝ)*X 1 1+(2284081109/5000000000 : ℝ)*X 1 2+(4215032571/10000000000 : ℝ)*X 2 0+(485427219/1250000000 : ℝ)*X 2 1+(2284081109/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-342388399/2000000000 : ℝ)*X 0 0+(5182633769/10000000000 : ℝ)*X 0 1+(1091643687/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((211188661/400000000 : ℝ)*X 1 0+(-19731061/125000000 : ℝ)*X 1 1+(2729109199/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055943331/2000000000 : ℝ)*X 2 0+(5458218303/10000000000 : ℝ)*X 2 1+(-1578484833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4215205783/10000000000 : ℝ)*X 0 0+(91261637/200000000 : ℝ)*X 0 1+(1944275639/5000000000 : ℝ)*X 0 2+(4215205783/10000000000 : ℝ)*X 1 0+(91261637/200000000 : ℝ)*X 1 1+(1944275639/5000000000 : ℝ)*X 1 2+(4215205783/10000000000 : ℝ)*X 2 0+(91261637/200000000 : ℝ)*X 2 1+(1944275639/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1607_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44548123275062089568439/14830000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62340731/12500000000000 : ℝ)*(base19) + (463773751/100000000000000 : ℝ)*(base23) + (7926813/50000000000000 : ℝ)*(lower2) + (18410299/25000000000000 : ℝ)*(upper3) + (54132497/100000000000000 : ℝ)*(upper5) + (1258735666360573/50000000000000 : ℝ)*(major0) + (1258735666360573/50000000000000 : ℝ)*(major1) + (1258735666360573/50000000000000 : ℝ)*(major2) + (3574532353993989/100000000000000 : ℝ)*(sp0) + (714907607970013/20000000000000 : ℝ)*(sp1) + (1787269037401081/50000000000000 : ℝ)*(sp2) + (730200645013307/50000000000000 : ℝ)*(sp3) + (1546145481/25000000000000 : ℝ)*(sp4) + (1368354559/50000000000000 : ℝ)*(sp7) + (365101006683933/25000000000000 : ℝ)*(f.failure) + (3574538538575913/100000000000000 : ℝ)*(f.sum) + (32267341074089/14830000000000000000000000000 : ℝ)*base65 + (7896041842654225937/1483000000000000000000000000000000 : ℝ)*base67 + (2764726768048225937/1483000000000000000000000000000000 : ℝ)*base69 + (5989972374529774063/1483000000000000000000000000000000 : ℝ)*base72 + (34343852548579/14830000000000000000000000000 : ℝ)*base73 + (5838317276853774063/1483000000000000000000000000000000 : ℝ)*base76 + (731119483815774063/1483000000000000000000000000000000 : ℝ)*base78 + (9846786544126225937/1483000000000000000000000000000000 : ℝ)*base79 + (15228563914239/14830000000000000000000000000 : ℝ)*base81 + (237209/31250000000000000000 : ℝ)*base89 + (237209/31250000000000000000 : ℝ)*base91 + (237209/31250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12367869943248291430644407151/1483000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (713554801/50000000000000 : ℝ)*(base19) + (1655114171/100000000000000 : ℝ)*(base23) + (238908861/50000000000000 : ℝ)*(lower1) + (39229587/25000000000000 : ℝ)*(upper3) + (66250297/100000000000000 : ℝ)*(lower4) + (232464151/100000000000000 : ℝ)*(upper5) + (2555568863009807/100000000000000 : ℝ)*(major0) + (2555568863009807/100000000000000 : ℝ)*(major1) + (2555568863009807/100000000000000 : ℝ)*(major2) + (468478879/50000000000000 : ℝ)*(sp2) + (1814316378926281/50000000000000 : ℝ)*(sp4) + (45357891634287/1250000000000 : ℝ)*(sp5) + (453578770722579/12500000000000 : ℝ)*(sp6) + (1482504690174909/100000000000000 : ℝ)*(sp7) + (1482504690174909/100000000000000 : ℝ)*(f.failure) + (1814316378926281/50000000000000 : ℝ)*(f.sum) + (15859791182001/29660000000000000000000000000 : ℝ)*base65 + (75321375857699914283/2966000000000000000000000000000000 : ℝ)*base67 + (6541033101395914283/2966000000000000000000000000000000 : ℝ)*base69 + (98927104972054085717/2966000000000000000000000000000000 : ℝ)*base72 + (169951189848379/29660000000000000000000000000 : ℝ)*base74 + (59780499409864085717/2966000000000000000000000000000000 : ℝ)*base76 + (10489903799697914283/2966000000000000000000000000000000 : ℝ)*base77 + (21968484814939914283/2966000000000000000000000000000000 : ℝ)*base79 + (8223963582139/29660000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (440657/125000000000000000000 : ℝ)*base89 + (440657/125000000000000000000 : ℝ)*base91 + (440657/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1607_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16347/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2083/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (651/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1607_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1607_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16507/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10271/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (651/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1607_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1607_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1607_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4743/1024 : ℝ) ≤ p) (hpb : p ≤ (4747/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2154773/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16507/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10271/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (651/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1607_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1531_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:05:28.436465+00:00
-- url     : https://prove2.me/submissions/0124dd3b-e92a-4658-803d-8454a4da6bef

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
theorem support_rectangle_w1531_s6_0 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675255331/5000000000 : ℝ)*x 0 + (5218543527/10000000000 : ℝ)*x 1 + (-1948963469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675255331/5000000000 : ℝ)^4559 ≤ (44639385713841/100000000000000 : ℝ)^3535 := by
    have hnat : (2675255331 : ℕ)^4559*100000000000000^3535 ≤ 44639385713841^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675255331 5000000000 44639385713841 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218543527/10000000000 : ℝ)^4559 ≤ (8644910316061/20000000000000 : ℝ)^3535 := by
    have hnat : (5218543527 : ℕ)^4559*20000000000000^3535 ≤ 8644910316061^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218543527 10000000000 8644910316061 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1948963469/10000000000 : ℝ)^4559 ≤ (94812989803/781250000000 : ℝ)^3535 := by
    have hnat : (1948963469 : ℕ)^4559*781250000000^3535 ≤ 94812989803^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948963469 10000000000 94812989803 781250000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675255331/5000000000 : ℝ), (5218543527/10000000000 : ℝ), (-1948963469/10000000000 : ℝ)] ![(44639385713841/100000000000000 : ℝ), (8644910316061/20000000000000 : ℝ), (94812989803/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675255331/5000000000 : ℝ)|^4559 ≤ (44639385713841/100000000000000 : ℝ)^3535
        have hw : |(2675255331/5000000000 : ℝ)|=(2675255331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218543527/10000000000 : ℝ)|^4559 ≤ (8644910316061/20000000000000 : ℝ)^3535
        have hw : |(5218543527/10000000000 : ℝ)|=(5218543527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1948963469/10000000000 : ℝ)|^4559 ≤ (94812989803/781250000000 : ℝ)^3535
        have hw : |(-1948963469/10000000000 : ℝ)|=(1948963469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s6_1 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1840336451/10000000000 : ℝ)*x 0 + (1043927401/2000000000 : ℝ)*x 1 + (2714834023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1840336451/10000000000 : ℝ)^4559 ≤ (1408855914943/12500000000000 : ℝ)^3535 := by
    have hnat : (1840336451 : ℕ)^4559*12500000000000^3535 ≤ 1408855914943^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840336451 10000000000 1408855914943 12500000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043927401/2000000000 : ℝ)^4559 ≤ (21618116351553/50000000000000 : ℝ)^3535 := by
    have hnat : (1043927401 : ℕ)^4559*50000000000000^3535 ≤ 21618116351553^3535*2000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043927401 2000000000 21618116351553 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714834023/5000000000 : ℝ)^4559 ≤ (2274645997981/5000000000000 : ℝ)^3535 := by
    have hnat : (2714834023 : ℕ)^4559*5000000000000^3535 ≤ 2274645997981^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714834023 5000000000 2274645997981 5000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1840336451/10000000000 : ℝ), (1043927401/2000000000 : ℝ), (2714834023/5000000000 : ℝ)] ![(1408855914943/12500000000000 : ℝ), (21618116351553/50000000000000 : ℝ), (2274645997981/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1840336451/10000000000 : ℝ)|^4559 ≤ (1408855914943/12500000000000 : ℝ)^3535
        have hw : |(-1840336451/10000000000 : ℝ)|=(1840336451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043927401/2000000000 : ℝ)|^4559 ≤ (21618116351553/50000000000000 : ℝ)^3535
        have hw : |(1043927401/2000000000 : ℝ)|=(1043927401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714834023/5000000000 : ℝ)|^4559 ≤ (2274645997981/5000000000000 : ℝ)^3535
        have hw : |(2714834023/5000000000 : ℝ)|=(2714834023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s6_2 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294646729/10000000000 : ℝ)*x 0 + (-1737834701/10000000000 : ℝ)*x 1 + (5429668071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294646729/10000000000 : ℝ)^4559 ≤ (22019606825323/50000000000000 : ℝ)^3535 := by
    have hnat : (5294646729 : ℕ)^4559*50000000000000^3535 ≤ 22019606825323^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294646729 10000000000 22019606825323 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1737834701/10000000000 : ℝ)^4559 ≤ (10467866104307/100000000000000 : ℝ)^3535 := by
    have hnat : (1737834701 : ℕ)^4559*100000000000000^3535 ≤ 10467866104307^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737834701 10000000000 10467866104307 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429668071/10000000000 : ℝ)^4559 ≤ (45492920229761/100000000000000 : ℝ)^3535 := by
    have hnat : (5429668071 : ℕ)^4559*100000000000000^3535 ≤ 45492920229761^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429668071 10000000000 45492920229761 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294646729/10000000000 : ℝ), (-1737834701/10000000000 : ℝ), (5429668071/10000000000 : ℝ)] ![(22019606825323/50000000000000 : ℝ), (10467866104307/100000000000000 : ℝ), (45492920229761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294646729/10000000000 : ℝ)|^4559 ≤ (22019606825323/50000000000000 : ℝ)^3535
        have hw : |(5294646729/10000000000 : ℝ)|=(5294646729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1737834701/10000000000 : ℝ)|^4559 ≤ (10467866104307/100000000000000 : ℝ)^3535
        have hw : |(-1737834701/10000000000 : ℝ)|=(1737834701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429668071/10000000000 : ℝ)|^4559 ≤ (45492920229761/100000000000000 : ℝ)^3535
        have hw : |(5429668071/10000000000 : ℝ)|=(5429668071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s6_3 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294646721/10000000000 : ℝ)*x 0 + (5429668067/10000000000 : ℝ)*x 1 + (-868917359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294646721/10000000000 : ℝ)^4559 ≤ (44039213564829/100000000000000 : ℝ)^3535 := by
    have hnat : (5294646721 : ℕ)^4559*100000000000000^3535 ≤ 44039213564829^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294646721 10000000000 44039213564829 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429668067/10000000000 : ℝ)^4559 ≤ (22746460093269/50000000000000 : ℝ)^3535 := by
    have hnat : (5429668067 : ℕ)^4559*50000000000000^3535 ≤ 22746460093269^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429668067 10000000000 22746460093269 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (868917359/5000000000 : ℝ)^4559 ≤ (10467866236369/100000000000000 : ℝ)^3535 := by
    have hnat : (868917359 : ℕ)^4559*100000000000000^3535 ≤ 10467866236369^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868917359 5000000000 10467866236369 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294646721/10000000000 : ℝ), (5429668067/10000000000 : ℝ), (-868917359/5000000000 : ℝ)] ![(44039213564829/100000000000000 : ℝ), (22746460093269/50000000000000 : ℝ), (10467866236369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294646721/10000000000 : ℝ)|^4559 ≤ (44039213564829/100000000000000 : ℝ)^3535
        have hw : |(5294646721/10000000000 : ℝ)|=(5294646721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429668067/10000000000 : ℝ)|^4559 ≤ (22746460093269/50000000000000 : ℝ)^3535
        have hw : |(5429668067/10000000000 : ℝ)|=(5429668067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-868917359/5000000000 : ℝ)|^4559 ≤ (10467866236369/100000000000000 : ℝ)^3535
        have hw : |(-868917359/5000000000 : ℝ)|=(868917359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_s6_4 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (426106997/1000000000 : ℝ)*x 0 + (17610039/39062500 : ℝ)*x 1 + (2012761727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426106997/1000000000 : ℝ)^4559 ≤ (33281247980021/100000000000000 : ℝ)^3535 := by
    have hnat : (426106997 : ℕ)^4559*100000000000000^3535 ≤ 33281247980021^3535*1000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426106997 1000000000 33281247980021 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17610039/39062500 : ℝ)^4559 ≤ (8947731302109/25000000000000 : ℝ)^3535 := by
    have hnat : (17610039 : ℕ)^4559*25000000000000^3535 ≤ 8947731302109^3535*39062500^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17610039 39062500 8947731302109 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2012761727/5000000000 : ℝ)^4559 ≤ (15463913400811/50000000000000 : ℝ)^3535 := by
    have hnat : (2012761727 : ℕ)^4559*50000000000000^3535 ≤ 15463913400811^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012761727 5000000000 15463913400811 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(426106997/1000000000 : ℝ), (17610039/39062500 : ℝ), (2012761727/5000000000 : ℝ)] ![(33281247980021/100000000000000 : ℝ), (8947731302109/25000000000000 : ℝ), (15463913400811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(426106997/1000000000 : ℝ)|^4559 ≤ (33281247980021/100000000000000 : ℝ)^3535
        have hw : |(426106997/1000000000 : ℝ)|=(426106997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17610039/39062500 : ℝ)|^4559 ≤ (8947731302109/25000000000000 : ℝ)^3535
        have hw : |(17610039/39062500 : ℝ)|=(17610039/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2012761727/5000000000 : ℝ)|^4559 ≤ (15463913400811/50000000000000 : ℝ)^3535
        have hw : |(2012761727/5000000000 : ℝ)|=(2012761727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1531_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10987/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10987/100000 : ℝ) ^ (4557/1024 : ℝ) ≤ (134792207075973/2500000000000000000 : ℝ) := by
    have hpowers : (10987/100000 : ℝ)^4557 ≤ (134792207075973/2500000000000000000 : ℝ)^1024 := by
      have hnat : (10987 : ℕ)^4557*2500000000000000000^1024 ≤ 134792207075973^1024*100000^4557 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10987 100000 134792207075973 2500000000000000000 4557 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10987/100000 : ℝ)) (X := (134792207075973/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4557/1024 : ℝ) ≤ (24828281611335243/100000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4557 ≤ (24828281611335243/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4557*100000000000000000000^1024 ≤ 24828281611335243^1024*20000^4557 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 24828281611335243 100000000000000000000 4557 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (24828281611335243/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250134792207075973/1250000000000000000 : ℝ) ≤ (500012115115269/500000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (1250134792207075973/1250000000000000000 : ℝ)^1024 ≤ (500012115115269/500000000000000 : ℝ)^4557 := by
      have hnat : (1250134792207075973 : ℕ)^1024*500000000000000^4557 ≤ 500012115115269^4557*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250134792207075973 1250000000000000000 500012115115269 500000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500012115115269/500000000000000 : ℝ)) (X := (1250134792207075973/1250000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030219969894374163/100000000000000000000 : ℝ) ≤ (2500169747776487/2500000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (100030219969894374163/100000000000000000000 : ℝ)^1024 ≤ (2500169747776487/2500000000000000 : ℝ)^4557 := by
      have hnat : (100030219969894374163 : ℕ)^1024*2500000000000000^4557 ≤ 2500169747776487^4557*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030219969894374163 100000000000000000000 2500169747776487 2500000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500169747776487/2500000000000000 : ℝ)) (X := (100030219969894374163/100000000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024828281611335243/50000000000000000000 : ℝ) ≤ (2500278919976629/2500000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (50024828281611335243/50000000000000000000 : ℝ)^1024 ≤ (2500278919976629/2500000000000000 : ℝ)^4557 := by
      have hnat : (50024828281611335243 : ℕ)^1024*2500000000000000^4557 ≤ 2500278919976629^4557*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024828281611335243 50000000000000000000 2500278919976629 2500000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500278919976629/2500000000000000 : ℝ)) (X := (50024828281611335243/50000000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(134792207075973/2500000000000000000 : ℝ) ≤ ((5621436759508239751/5622500000000000000 : ℝ)+2*(54586100071/56225000000000 : ℝ)*(10987/100000 : ℝ))^(4557/1024 : ℝ) := by
    rw [show (5621436759508239751/5622500000000000000 : ℝ)+2*(54586100071/56225000000000 : ℝ)*(10987/100000 : ℝ)=(500012115115269/500000000000000 : ℝ) by norm_num, show 1+2*(134792207075973/2500000000000000000 : ℝ)=(1250134792207075973/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24828281611335243/100000000000000000000 : ℝ)+(134792207075973/2500000000000000000 : ℝ) ≤ ((5621436759508239751/5622500000000000000 : ℝ)+(54586100071/56225000000000 : ℝ)*((3097/20000 : ℝ)+(10987/100000 : ℝ)))^(4557/1024 : ℝ) := by
    rw [show (5621436759508239751/5622500000000000000 : ℝ)+(54586100071/56225000000000 : ℝ)*((3097/20000 : ℝ)+(10987/100000 : ℝ))=(2500169747776487/2500000000000000 : ℝ) by norm_num, show 1+(24828281611335243/100000000000000000000 : ℝ)+(134792207075973/2500000000000000000 : ℝ)=(100030219969894374163/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24828281611335243/100000000000000000000 : ℝ) ≤ ((5621436759508239751/5622500000000000000 : ℝ)+2*(54586100071/56225000000000 : ℝ)*(3097/20000 : ℝ))^(4557/1024 : ℝ) := by
    rw [show (5621436759508239751/5622500000000000000 : ℝ)+2*(54586100071/56225000000000 : ℝ)*(3097/20000 : ℝ)=(2500278919976629/2500000000000000 : ℝ) by norm_num, show 1+2*(24828281611335243/100000000000000000000 : ℝ)=(50024828281611335243/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5621436759508239751/5622500000000000000 : ℝ)*(X 1 0+X 2 0)+(54586100071/56225000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (10987/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (5621436759508239751/5622500000000000000 : ℝ)) (alpha := (54586100071/56225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5621436759508239751/5622500000000000000 : ℝ)*(X 0 1+X 2 1)+(54586100071/56225000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (10987/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (5621436759508239751/5622500000000000000 : ℝ)) (alpha := (54586100071/56225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5621436759508239751/5622500000000000000 : ℝ)*(X 0 2+X 1 2)+(54586100071/56225000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (10987/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (5621436759508239751/5622500000000000000 : ℝ)) (alpha := (54586100071/56225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2675255331/5000000000 : ℝ)*X 2 0+(5218543527/10000000000 : ℝ)*X 2 1+(-1948963469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s6_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1840336451/10000000000 : ℝ)*X 0 0+(1043927401/2000000000 : ℝ)*X 0 1+(2714834023/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5294646729/10000000000 : ℝ)*X 1 0+(-1737834701/10000000000 : ℝ)*X 1 1+(5429668071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5294646721/10000000000 : ℝ)*X 2 0+(5429668067/10000000000 : ℝ)*X 2 1+(-868917359/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((426106997/1000000000 : ℝ)*X 0 0+(17610039/39062500 : ℝ)*X 0 1+(2012761727/5000000000 : ℝ)*X 0 2+(426106997/1000000000 : ℝ)*X 1 0+(17610039/39062500 : ℝ)*X 1 1+(2012761727/5000000000 : ℝ)*X 1 2+(426106997/1000000000 : ℝ)*X 2 0+(17610039/39062500 : ℝ)*X 2 1+(2012761727/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (70083154883439617702254677/8785156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (661075997/50000000000000 : ℝ)*(base19) + (1359389807/100000000000000 : ℝ)*(base23) + (451451391/100000000000000 : ℝ)*(lower1) + (164718907/100000000000000 : ℝ)*(upper3) + (23062101/100000000000000 : ℝ)*(lower4) + (43386053/25000000000000 : ℝ)*(upper5) + (427067473809493/12500000000000 : ℝ)*(major0) + (427067473809493/12500000000000 : ℝ)*(major1) + (427067473809493/12500000000000 : ℝ)*(major2) + (82870073/100000000000000 : ℝ)*(sp0) + (297573704858527/6250000000000 : ℝ)*(sp1) + (2380588977792219/50000000000000 : ℝ)*(sp2) + (595147229434569/12500000000000 : ℝ)*(sp3) + (517975009325101/25000000000000 : ℝ)*(sp4) + (517975009325101/25000000000000 : ℝ)*(f.failure) + (297573704858527/6250000000000 : ℝ)*(f.sum) + (1703076012083/1405625000000000000000000000 : ℝ)*base66 + (131492994883880289/5406250000000000000000000000000 : ℝ)*base68 + (109622484053130289/5406250000000000000000000000000 : ℝ)*base70 + (181591261980067789/5406250000000000000000000000000 : ℝ)*base72 + (16583450059043/5622500000000000000000000000 : ℝ)*base73 + (24924875006307211/5406250000000000000000000000000 : ℝ)*base75 + (23330867472817789/5406250000000000000000000000000 : ℝ)*base78 + (99347250166224039/5406250000000000000000000000000 : ℝ)*base80 + (117998390566439/11245000000000000000000000000 : ℝ)*base82 + (4523259/312500000000000000000 : ℝ)*base89 + (4523259/312500000000000000000 : ℝ)*base91 + (4523259/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1531_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1531_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1531_box_0 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-81500871/500000000 : ℝ)*x 0 + (5400782481/10000000000 : ℝ)*x 1 + (216031267/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81500871/500000000 : ℝ)^4559 ≤ (9637941485029/100000000000000 : ℝ)^3535 := by
    have hnat : (81500871 : ℕ)^4559*100000000000000^3535 ≤ 9637941485029^3535*500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81500871 500000000 9637941485029 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400782481/10000000000 : ℝ)^4559 ≤ (45181033595769/100000000000000 : ℝ)^3535 := by
    have hnat : (5400782481 : ℕ)^4559*100000000000000^3535 ≤ 45181033595769^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400782481 10000000000 45181033595769 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216031267/400000000 : ℝ)^4559 ≤ (22590512449933/50000000000000 : ℝ)^3535 := by
    have hnat : (216031267 : ℕ)^4559*50000000000000^3535 ≤ 22590512449933^3535*400000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216031267 400000000 22590512449933 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-81500871/500000000 : ℝ), (5400782481/10000000000 : ℝ), (216031267/400000000 : ℝ)] ![(9637941485029/100000000000000 : ℝ), (45181033595769/100000000000000 : ℝ), (22590512449933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-81500871/500000000 : ℝ)|^4559 ≤ (9637941485029/100000000000000 : ℝ)^3535
        have hw : |(-81500871/500000000 : ℝ)|=(81500871/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400782481/10000000000 : ℝ)|^4559 ≤ (45181033595769/100000000000000 : ℝ)^3535
        have hw : |(5400782481/10000000000 : ℝ)|=(5400782481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216031267/400000000 : ℝ)|^4559 ≤ (22590512449933/50000000000000 : ℝ)^3535
        have hw : |(216031267/400000000 : ℝ)|=(216031267/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_box_1 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82359037/156250000 : ℝ)*x 0 + (-362042381/2000000000 : ℝ)*x 1 + (1080156563/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82359037/156250000 : ℝ)^4559 ≤ (43785485093821/100000000000000 : ℝ)^3535 := by
    have hnat : (82359037 : ℕ)^4559*100000000000000^3535 ≤ 43785485093821^3535*156250000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82359037 156250000 43785485093821 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (362042381/2000000000 : ℝ)^4559 ≤ (2758369426101/25000000000000 : ℝ)^3535 := by
    have hnat : (362042381 : ℕ)^4559*25000000000000^3535 ≤ 2758369426101^3535*2000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362042381 2000000000 2758369426101 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080156563/2000000000 : ℝ)^4559 ≤ (22590518599641/50000000000000 : ℝ)^3535 := by
    have hnat : (1080156563 : ℕ)^4559*50000000000000^3535 ≤ 22590518599641^3535*2000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080156563 2000000000 22590518599641 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82359037/156250000 : ℝ), (-362042381/2000000000 : ℝ), (1080156563/2000000000 : ℝ)] ![(43785485093821/100000000000000 : ℝ), (2758369426101/25000000000000 : ℝ), (22590518599641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82359037/156250000 : ℝ)|^4559 ≤ (43785485093821/100000000000000 : ℝ)^3535
        have hw : |(82359037/156250000 : ℝ)|=(82359037/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-362042381/2000000000 : ℝ)|^4559 ≤ (2758369426101/25000000000000 : ℝ)^3535
        have hw : |(-362042381/2000000000 : ℝ)|=(362042381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080156563/2000000000 : ℝ)|^4559 ≤ (22590518599641/50000000000000 : ℝ)^3535
        have hw : |(1080156563/2000000000 : ℝ)|=(1080156563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_box_2 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317744569/2500000000 : ℝ)*x 0 + (5400782909/10000000000 : ℝ)*x 1 + (-18102119/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317744569/2500000000 : ℝ)^4559 ≤ (43785484108207/100000000000000 : ℝ)^3535 := by
    have hnat : (1317744569 : ℕ)^4559*100000000000000^3535 ≤ 43785484108207^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317744569 2500000000 43785484108207 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400782909/10000000000 : ℝ)^4559 ≤ (11295259553361/25000000000000 : ℝ)^3535 := by
    have hnat : (5400782909 : ℕ)^4559*25000000000000^3535 ≤ 11295259553361^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400782909 10000000000 11295259553361 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18102119/100000000 : ℝ)^4559 ≤ (11033477665101/100000000000000 : ℝ)^3535 := by
    have hnat : (18102119 : ℕ)^4559*100000000000000^3535 ≤ 11033477665101^3535*100000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18102119 100000000 11033477665101 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317744569/2500000000 : ℝ), (5400782909/10000000000 : ℝ), (-18102119/100000000 : ℝ)] ![(43785484108207/100000000000000 : ℝ), (11295259553361/25000000000000 : ℝ), (11033477665101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317744569/2500000000 : ℝ)|^4559 ≤ (43785484108207/100000000000000 : ℝ)^3535
        have hw : |(1317744569/2500000000 : ℝ)|=(1317744569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400782909/10000000000 : ℝ)|^4559 ≤ (11295259553361/25000000000000 : ℝ)^3535
        have hw : |(5400782909/10000000000 : ℝ)|=(5400782909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18102119/100000000 : ℝ)|^4559 ≤ (11033477665101/100000000000000 : ℝ)^3535
        have hw : |(-18102119/100000000 : ℝ)|=(18102119/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_box_3 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2231618679/5000000000 : ℝ)*x 0 + (4166751511/10000000000 : ℝ)*x 1 + (4166751397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2231618679/5000000000 : ℝ)^4559 ≤ (35331530767589/100000000000000 : ℝ)^3535 := by
    have hnat : (2231618679 : ℕ)^4559*100000000000000^3535 ≤ 35331530767589^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231618679 5000000000 35331530767589 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4166751511/10000000000 : ℝ)^4559 ≤ (505222424717/1562500000000 : ℝ)^3535 := by
    have hnat : (4166751511 : ℕ)^4559*1562500000000^3535 ≤ 505222424717^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166751511 10000000000 505222424717 1562500000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4166751397/10000000000 : ℝ)^4559 ≤ (32334234040981/100000000000000 : ℝ)^3535 := by
    have hnat : (4166751397 : ℕ)^4559*100000000000000^3535 ≤ 32334234040981^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166751397 10000000000 32334234040981 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2231618679/5000000000 : ℝ), (4166751511/10000000000 : ℝ), (4166751397/10000000000 : ℝ)] ![(35331530767589/100000000000000 : ℝ), (505222424717/1562500000000 : ℝ), (32334234040981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2231618679/5000000000 : ℝ)|^4559 ≤ (35331530767589/100000000000000 : ℝ)^3535
        have hw : |(2231618679/5000000000 : ℝ)|=(2231618679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4166751511/10000000000 : ℝ)|^4559 ≤ (505222424717/1562500000000 : ℝ)^3535
        have hw : |(4166751511/10000000000 : ℝ)|=(4166751511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4166751397/10000000000 : ℝ)|^4559 ≤ (32334234040981/100000000000000 : ℝ)^3535
        have hw : |(4166751397/10000000000 : ℝ)|=(4166751397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_box_4 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1028013173/5000000000 : ℝ)*x 0 + (1048837797/2000000000 : ℝ)*x 1 + (5244188843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1028013173/5000000000 : ℝ)^4559 ≤ (13002608176091/100000000000000 : ℝ)^3535 := by
    have hnat : (1028013173 : ℕ)^4559*100000000000000^3535 ≤ 13002608176091^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028013173 5000000000 13002608176091 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048837797/2000000000 : ℝ)^4559 ≤ (5437337083669/12500000000000 : ℝ)^3535 := by
    have hnat : (1048837797 : ℕ)^4559*12500000000000^3535 ≤ 5437337083669^3535*2000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048837797 2000000000 5437337083669 12500000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244188843/10000000000 : ℝ)^4559 ≤ (43498695150321/100000000000000 : ℝ)^3535 := by
    have hnat : (5244188843 : ℕ)^4559*100000000000000^3535 ≤ 43498695150321^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244188843 10000000000 43498695150321 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1028013173/5000000000 : ℝ), (1048837797/2000000000 : ℝ), (5244188843/10000000000 : ℝ)] ![(13002608176091/100000000000000 : ℝ), (5437337083669/12500000000000 : ℝ), (43498695150321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1028013173/5000000000 : ℝ)|^4559 ≤ (13002608176091/100000000000000 : ℝ)^3535
        have hw : |(-1028013173/5000000000 : ℝ)|=(1028013173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048837797/2000000000 : ℝ)|^4559 ≤ (5437337083669/12500000000000 : ℝ)^3535
        have hw : |(1048837797/2000000000 : ℝ)|=(1048837797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244188843/10000000000 : ℝ)|^4559 ≤ (43498695150321/100000000000000 : ℝ)^3535
        have hw : |(5244188843/10000000000 : ℝ)|=(5244188843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_box_5 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344960983/2500000000 : ℝ)*x 0 + (-1875084607/10000000000 : ℝ)*x 1 + (1311047207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344960983/2500000000 : ℝ)^4559 ≤ (5619406920229/12500000000000 : ℝ)^3535 := by
    have hnat : (1344960983 : ℕ)^4559*12500000000000^3535 ≤ 5619406920229^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344960983 2500000000 5619406920229 12500000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1875084607/10000000000 : ℝ)^4559 ≤ (11546049633391/100000000000000 : ℝ)^3535 := by
    have hnat : (1875084607 : ℕ)^4559*100000000000000^3535 ≤ 11546049633391^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875084607 10000000000 11546049633391 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311047207/2500000000 : ℝ)^4559 ≤ (2174934749493/5000000000000 : ℝ)^3535 := by
    have hnat : (1311047207 : ℕ)^4559*5000000000000^3535 ≤ 2174934749493^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311047207 2500000000 2174934749493 5000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344960983/2500000000 : ℝ), (-1875084607/10000000000 : ℝ), (1311047207/2500000000 : ℝ)] ![(5619406920229/12500000000000 : ℝ), (11546049633391/100000000000000 : ℝ), (2174934749493/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344960983/2500000000 : ℝ)|^4559 ≤ (5619406920229/12500000000000 : ℝ)^3535
        have hw : |(1344960983/2500000000 : ℝ)|=(1344960983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1875084607/10000000000 : ℝ)|^4559 ≤ (11546049633391/100000000000000 : ℝ)^3535
        have hw : |(-1875084607/10000000000 : ℝ)|=(1875084607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311047207/2500000000 : ℝ)|^4559 ≤ (2174934749493/5000000000000 : ℝ)^3535
        have hw : |(1311047207/2500000000 : ℝ)|=(1311047207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_box_6 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379844107/10000000000 : ℝ)*x 0 + (5244188767/10000000000 : ℝ)*x 1 + (-1875084451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379844107/10000000000 : ℝ)^4559 ≤ (44955257247777/100000000000000 : ℝ)^3535 := by
    have hnat : (5379844107 : ℕ)^4559*100000000000000^3535 ≤ 44955257247777^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379844107 10000000000 44955257247777 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244188767/10000000000 : ℝ)^4559 ≤ (43498694337319/100000000000000 : ℝ)^3535 := by
    have hnat : (5244188767 : ℕ)^4559*100000000000000^3535 ≤ 43498694337319^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244188767 10000000000 43498694337319 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1875084451/10000000000 : ℝ)^4559 ≤ (2309209678909/20000000000000 : ℝ)^3535 := by
    have hnat : (1875084451 : ℕ)^4559*20000000000000^3535 ≤ 2309209678909^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875084451 10000000000 2309209678909 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379844107/10000000000 : ℝ), (5244188767/10000000000 : ℝ), (-1875084451/10000000000 : ℝ)] ![(44955257247777/100000000000000 : ℝ), (43498694337319/100000000000000 : ℝ), (2309209678909/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379844107/10000000000 : ℝ)|^4559 ≤ (44955257247777/100000000000000 : ℝ)^3535
        have hw : |(5379844107/10000000000 : ℝ)|=(5379844107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244188767/10000000000 : ℝ)|^4559 ≤ (43498694337319/100000000000000 : ℝ)^3535
        have hw : |(5244188767/10000000000 : ℝ)|=(5244188767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1875084451/10000000000 : ℝ)|^4559 ≤ (2309209678909/20000000000000 : ℝ)^3535
        have hw : |(-1875084451/10000000000 : ℝ)|=(1875084451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_box_7 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2028131317/5000000000 : ℝ)*x 0 + (136565837/312500000 : ℝ)*x 1 + (4370107031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2028131317/5000000000 : ℝ)^4559 ≤ (78081854329/250000000000 : ℝ)^3535 := by
    have hnat : (2028131317 : ℕ)^4559*250000000000^3535 ≤ 78081854329^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028131317 5000000000 78081854329 250000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136565837/312500000 : ℝ)^4559 ≤ (68767255743/200000000000 : ℝ)^3535 := by
    have hnat : (136565837 : ℕ)^4559*200000000000^3535 ≤ 68767255743^3535*312500000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136565837 312500000 68767255743 200000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4370107031/10000000000 : ℝ)^4559 ≤ (17191815188911/50000000000000 : ℝ)^3535 := by
    have hnat : (4370107031 : ℕ)^4559*50000000000000^3535 ≤ 17191815188911^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370107031 10000000000 17191815188911 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2028131317/5000000000 : ℝ), (136565837/312500000 : ℝ), (4370107031/10000000000 : ℝ)] ![(78081854329/250000000000 : ℝ), (68767255743/200000000000 : ℝ), (17191815188911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2028131317/5000000000 : ℝ)|^4559 ≤ (78081854329/250000000000 : ℝ)^3535
        have hw : |(2028131317/5000000000 : ℝ)|=(2028131317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136565837/312500000 : ℝ)|^4559 ≤ (68767255743/200000000000 : ℝ)^3535
        have hw : |(136565837/312500000 : ℝ)|=(136565837/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4370107031/10000000000 : ℝ)|^4559 ≤ (17191815188911/50000000000000 : ℝ)^3535
        have hw : |(4370107031/10000000000 : ℝ)|=(4370107031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_box_8 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-122869003/625000000 : ℝ)*x 0 + (320892361/625000000 : ℝ)*x 1 + (1084235621/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (122869003/625000000 : ℝ)^4559 ≤ (12272278600827/100000000000000 : ℝ)^3535 := by
    have hnat : (122869003 : ℕ)^4559*100000000000000^3535 ≤ 12272278600827^3535*625000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122869003 625000000 12272278600827 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (320892361/625000000 : ℝ)^4559 ≤ (8465303985627/20000000000000 : ℝ)^3535 := by
    have hnat : (320892361 : ℕ)^4559*20000000000000^3535 ≤ 8465303985627^3535*625000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320892361 625000000 8465303985627 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084235621/2000000000 : ℝ)^4559 ≤ (22700600726201/50000000000000 : ℝ)^3535 := by
    have hnat : (1084235621 : ℕ)^4559*50000000000000^3535 ≤ 22700600726201^3535*2000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084235621 2000000000 22700600726201 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-122869003/625000000 : ℝ), (320892361/625000000 : ℝ), (1084235621/2000000000 : ℝ)] ![(12272278600827/100000000000000 : ℝ), (8465303985627/20000000000000 : ℝ), (22700600726201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-122869003/625000000 : ℝ)|^4559 ≤ (12272278600827/100000000000000 : ℝ)^3535
        have hw : |(-122869003/625000000 : ℝ)|=(122869003/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(320892361/625000000 : ℝ)|^4559 ≤ (8465303985627/20000000000000 : ℝ)^3535
        have hw : |(320892361/625000000 : ℝ)|=(320892361/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084235621/2000000000 : ℝ)|^4559 ≤ (22700600726201/50000000000000 : ℝ)^3535
        have hw : |(1084235621/2000000000 : ℝ)|=(1084235621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_box_9 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105135891/200000000 : ℝ)*x 0 + (-1801520919/10000000000 : ℝ)*x 1 + (5421178151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105135891/200000000 : ℝ)^4559 ≤ (10908397578397/25000000000000 : ℝ)^3535 := by
    have hnat : (105135891 : ℕ)^4559*25000000000000^3535 ≤ 10908397578397^3535*200000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105135891 200000000 10908397578397 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1801520919/10000000000 : ℝ)^4559 ≤ (10965207723429/100000000000000 : ℝ)^3535 := by
    have hnat : (1801520919 : ℕ)^4559*100000000000000^3535 ≤ 10965207723429^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1801520919 10000000000 10965207723429 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421178151/10000000000 : ℝ)^4559 ≤ (45401201949237/100000000000000 : ℝ)^3535 := by
    have hnat : (5421178151 : ℕ)^4559*100000000000000^3535 ≤ 45401201949237^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421178151 10000000000 45401201949237 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105135891/200000000 : ℝ), (-1801520919/10000000000 : ℝ), (5421178151/10000000000 : ℝ)] ![(10908397578397/25000000000000 : ℝ), (10965207723429/100000000000000 : ℝ), (45401201949237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105135891/200000000 : ℝ)|^4559 ≤ (10908397578397/25000000000000 : ℝ)^3535
        have hw : |(105135891/200000000 : ℝ)|=(105135891/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1801520919/10000000000 : ℝ)|^4559 ≤ (10965207723429/100000000000000 : ℝ)^3535
        have hw : |(-1801520919/10000000000 : ℝ)|=(1801520919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421178151/10000000000 : ℝ)|^4559 ≤ (45401201949237/100000000000000 : ℝ)^3535
        have hw : |(5421178151/10000000000 : ℝ)|=(5421178151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_box_10 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628397317/5000000000 : ℝ)*x 0 + (5421177963/10000000000 : ℝ)*x 1 + (-1801521063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628397317/5000000000 : ℝ)^4559 ≤ (8726718242559/20000000000000 : ℝ)^3535 := by
    have hnat : (2628397317 : ℕ)^4559*20000000000000^3535 ≤ 8726718242559^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628397317 5000000000 8726718242559 20000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421177963/10000000000 : ℝ)^4559 ≤ (5675149989837/12500000000000 : ℝ)^3535 := by
    have hnat : (5421177963 : ℕ)^4559*12500000000000^3535 ≤ 5675149989837^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421177963 10000000000 5675149989837 12500000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1801521063/10000000000 : ℝ)^4559 ≤ (5482604426899/50000000000000 : ℝ)^3535 := by
    have hnat : (1801521063 : ℕ)^4559*50000000000000^3535 ≤ 5482604426899^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1801521063 10000000000 5482604426899 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628397317/5000000000 : ℝ), (5421177963/10000000000 : ℝ), (-1801521063/10000000000 : ℝ)] ![(8726718242559/20000000000000 : ℝ), (5675149989837/12500000000000 : ℝ), (5482604426899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628397317/5000000000 : ℝ)|^4559 ≤ (8726718242559/20000000000000 : ℝ)^3535
        have hw : |(2628397317/5000000000 : ℝ)|=(2628397317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421177963/10000000000 : ℝ)|^4559 ≤ (5675149989837/12500000000000 : ℝ)^3535
        have hw : |(5421177963/10000000000 : ℝ)|=(5421177963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1801521063/10000000000 : ℝ)|^4559 ≤ (5482604426899/50000000000000 : ℝ)^3535
        have hw : |(-1801521063/10000000000 : ℝ)|=(1801521063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_box_11 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (180603757/400000000 : ℝ)*x 0 + (4140232879/10000000000 : ℝ)*x 1 + (4140232829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (180603757/400000000 : ℝ)^4559 ≤ (35861834433297/100000000000000 : ℝ)^3535 := by
    have hnat : (180603757 : ℕ)^4559*100000000000000^3535 ≤ 35861834433297^3535*400000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180603757 400000000 35861834433297 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4140232879/10000000000 : ℝ)^4559 ≤ (160345415133/500000000000 : ℝ)^3535 := by
    have hnat : (4140232879 : ℕ)^4559*500000000000^3535 ≤ 160345415133^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140232879 10000000000 160345415133 500000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4140232829/10000000000 : ℝ)^4559 ≤ (32069082527127/100000000000000 : ℝ)^3535 := by
    have hnat : (4140232829 : ℕ)^4559*100000000000000^3535 ≤ 32069082527127^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140232829 10000000000 32069082527127 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(180603757/400000000 : ℝ), (4140232879/10000000000 : ℝ), (4140232829/10000000000 : ℝ)] ![(35861834433297/100000000000000 : ℝ), (160345415133/500000000000 : ℝ), (32069082527127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(180603757/400000000 : ℝ)|^4559 ≤ (35861834433297/100000000000000 : ℝ)^3535
        have hw : |(180603757/400000000 : ℝ)|=(180603757/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4140232879/10000000000 : ℝ)|^4559 ≤ (160345415133/500000000000 : ℝ)^3535
        have hw : |(4140232879/10000000000 : ℝ)|=(4140232879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4140232829/10000000000 : ℝ)|^4559 ≤ (32069082527127/100000000000000 : ℝ)^3535
        have hw : |(4140232829/10000000000 : ℝ)|=(4140232829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_box_12 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-859994611/5000000000 : ℝ)*x 0 + (55072227/100000000 : ℝ)*x 1 + (2614574813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859994611/5000000000 : ℝ)^4559 ≤ (10329442520739/100000000000000 : ℝ)^3535 := by
    have hnat : (859994611 : ℕ)^4559*100000000000000^3535 ≤ 10329442520739^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859994611 5000000000 10329442520739 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55072227/100000000 : ℝ)^4559 ≤ (46332675914311/100000000000000 : ℝ)^3535 := by
    have hnat : (55072227 : ℕ)^4559*100000000000000^3535 ≤ 46332675914311^3535*100000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55072227 100000000 46332675914311 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614574813/5000000000 : ℝ)^4559 ≤ (21668940778317/50000000000000 : ℝ)^3535 := by
    have hnat : (2614574813 : ℕ)^4559*50000000000000^3535 ≤ 21668940778317^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614574813 5000000000 21668940778317 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-859994611/5000000000 : ℝ), (55072227/100000000 : ℝ), (2614574813/5000000000 : ℝ)] ![(10329442520739/100000000000000 : ℝ), (46332675914311/100000000000000 : ℝ), (21668940778317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-859994611/5000000000 : ℝ)|^4559 ≤ (10329442520739/100000000000000 : ℝ)^3535
        have hw : |(-859994611/5000000000 : ℝ)|=(859994611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(55072227/100000000 : ℝ)|^4559 ≤ (46332675914311/100000000000000 : ℝ)^3535
        have hw : |(55072227/100000000 : ℝ)|=(55072227/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614574813/5000000000 : ℝ)|^4559 ≤ (21668940778317/50000000000000 : ℝ)^3535
        have hw : |(2614574813/5000000000 : ℝ)|=(2614574813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_box_13 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5390299677/10000000000 : ℝ)*x 0 + (-188113931/1000000000 : ℝ)*x 1 + (65364367/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5390299677/10000000000 : ℝ)^4559 ≤ (22533983417457/50000000000000 : ℝ)^3535 := by
    have hnat : (5390299677 : ℕ)^4559*50000000000000^3535 ≤ 22533983417457^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390299677 10000000000 22533983417457 50000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188113931/1000000000 : ℝ)^4559 ≤ (2898538610201/25000000000000 : ℝ)^3535 := by
    have hnat : (188113931 : ℕ)^4559*25000000000000^3535 ≤ 2898538610201^3535*1000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188113931 1000000000 2898538610201 25000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65364367/125000000 : ℝ)^4559 ≤ (43337878713493/100000000000000 : ℝ)^3535 := by
    have hnat : (65364367 : ℕ)^4559*100000000000000^3535 ≤ 43337878713493^3535*125000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65364367 125000000 43337878713493 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5390299677/10000000000 : ℝ), (-188113931/1000000000 : ℝ), (65364367/125000000 : ℝ)] ![(22533983417457/50000000000000 : ℝ), (2898538610201/25000000000000 : ℝ), (43337878713493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5390299677/10000000000 : ℝ)|^4559 ≤ (22533983417457/50000000000000 : ℝ)^3535
        have hw : |(5390299677/10000000000 : ℝ)|=(5390299677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-188113931/1000000000 : ℝ)|^4559 ≤ (2898538610201/25000000000000 : ℝ)^3535
        have hw : |(-188113931/1000000000 : ℝ)|=(188113931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65364367/125000000 : ℝ)|^4559 ≤ (43337878713493/100000000000000 : ℝ)^3535
        have hw : |(65364367/125000000 : ℝ)|=(65364367/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_box_14 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347574939/2500000000 : ℝ)*x 0 + (2614574781/5000000000 : ℝ)*x 1 + (-188113893/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347574939/2500000000 : ℝ)^4559 ≤ (45067967686763/100000000000000 : ℝ)^3535 := by
    have hnat : (1347574939 : ℕ)^4559*100000000000000^3535 ≤ 45067967686763^3535*2500000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347574939 2500000000 45067967686763 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614574781/5000000000 : ℝ)^4559 ≤ (4333788087257/10000000000000 : ℝ)^3535 := by
    have hnat : (2614574781 : ℕ)^4559*10000000000000^3535 ≤ 4333788087257^3535*5000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614574781 5000000000 4333788087257 10000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188113893/1000000000 : ℝ)^4559 ≤ (11594151420283/100000000000000 : ℝ)^3535 := by
    have hnat : (188113893 : ℕ)^4559*100000000000000^3535 ≤ 11594151420283^3535*1000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188113893 1000000000 11594151420283 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347574939/2500000000 : ℝ), (2614574781/5000000000 : ℝ), (-188113893/1000000000 : ℝ)] ![(45067967686763/100000000000000 : ℝ), (4333788087257/10000000000000 : ℝ), (11594151420283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347574939/2500000000 : ℝ)|^4559 ≤ (45067967686763/100000000000000 : ℝ)^3535
        have hw : |(1347574939/2500000000 : ℝ)|=(1347574939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614574781/5000000000 : ℝ)|^4559 ≤ (4333788087257/10000000000000 : ℝ)^3535
        have hw : |(2614574781/5000000000 : ℝ)|=(2614574781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-188113893/1000000000 : ℝ)|^4559 ≤ (11594151420283/100000000000000 : ℝ)^3535
        have hw : |(-188113893/1000000000 : ℝ)|=(188113893/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1531_box_15 (p : ℝ) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (50203933/125000000 : ℝ)*x 0 + (4389614079/10000000000 : ℝ)*x 1 + (4389613477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50203933/125000000 : ℝ)^4559 ≤ (30836611663213/100000000000000 : ℝ)^3535 := by
    have hnat : (50203933 : ℕ)^4559*100000000000000^3535 ≤ 30836611663213^3535*125000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50203933 125000000 30836611663213 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4389614079/10000000000 : ℝ)^4559 ≤ (34581697218651/100000000000000 : ℝ)^3535 := by
    have hnat : (4389614079 : ℕ)^4559*100000000000000^3535 ≤ 34581697218651^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4389614079 10000000000 34581697218651 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4389613477/10000000000 : ℝ)^4559 ≤ (34581691102241/100000000000000 : ℝ)^3535 := by
    have hnat : (4389613477 : ℕ)^4559*100000000000000^3535 ≤ 34581691102241^3535*10000000000^4559 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4389613477 10000000000 34581691102241 100000000000000 4559 3535 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4559/1024 : ℝ)) 4559 3535 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(50203933/125000000 : ℝ), (4389614079/10000000000 : ℝ), (4389613477/10000000000 : ℝ)] ![(30836611663213/100000000000000 : ℝ), (34581697218651/100000000000000 : ℝ), (34581691102241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(50203933/125000000 : ℝ)|^4559 ≤ (30836611663213/100000000000000 : ℝ)^3535
        have hw : |(50203933/125000000 : ℝ)|=(50203933/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4389614079/10000000000 : ℝ)|^4559 ≤ (34581697218651/100000000000000 : ℝ)^3535
        have hw : |(4389614079/10000000000 : ℝ)|=(4389614079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4389613477/10000000000 : ℝ)|^4559 ≤ (34581691102241/100000000000000 : ℝ)^3535
        have hw : |(4389613477/10000000000 : ℝ)|=(4389613477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1531_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31883/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58717/100000 : ℝ) ∧ (80521/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86123/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10987/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10987/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10987/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10987/100000 : ℝ) ^ (4557/1024 : ℝ) ≤ (134792207075973/2500000000000000000 : ℝ) := by
    have hpowers : (10987/100000 : ℝ)^4557 ≤ (134792207075973/2500000000000000000 : ℝ)^1024 := by
      have hnat : (10987 : ℕ)^4557*2500000000000000000^1024 ≤ 134792207075973^1024*100000^4557 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10987 100000 134792207075973 2500000000000000000 4557 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10987/100000 : ℝ)) (X := (134792207075973/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4557/1024 : ℝ) ≤ (4964229413724081/20000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4557 ≤ (4964229413724081/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4557*20000000000000000000^1024 ≤ 4964229413724081^1024*25000^4557 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 4964229413724081 20000000000000000000 4557 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (4964229413724081/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250134792207075973/1250000000000000000 : ℝ) ≤ (500012115115269/500000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (1250134792207075973/1250000000000000000 : ℝ)^1024 ≤ (500012115115269/500000000000000 : ℝ)^4557 := by
      have hnat : (1250134792207075973 : ℕ)^1024*500000000000000^4557 ≤ 500012115115269^4557*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250134792207075973 1250000000000000000 500012115115269 500000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500012115115269/500000000000000 : ℝ)) (X := (1250134792207075973/1250000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001208513414066373/4000000000000000000 : ℝ) ≤ (10000678830823729/10000000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (4001208513414066373/4000000000000000000 : ℝ)^1024 ≤ (10000678830823729/10000000000000000 : ℝ)^4557 := by
      have hnat : (4001208513414066373 : ℕ)^1024*10000000000000000^4557 ≤ 10000678830823729^4557*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001208513414066373 4000000000000000000 10000678830823729 10000000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000678830823729/10000000000000000 : ℝ)) (X := (4001208513414066373/4000000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004964229413724081/10000000000000000000 : ℝ) ≤ (5000557679671039/5000000000000000 : ℝ) ^ (4557/1024 : ℝ) := by
    have hpowers : (10004964229413724081/10000000000000000000 : ℝ)^1024 ≤ (5000557679671039/5000000000000000 : ℝ)^4557 := by
      have hnat : (10004964229413724081 : ℕ)^1024*5000000000000000^4557 ≤ 5000557679671039^4557*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004964229413724081 10000000000000000000 5000557679671039 5000000000000000 1024 4557 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000557679671039/5000000000000000 : ℝ)) (X := (10004964229413724081/10000000000000000000 : ℝ)) (by norm_num) 4557 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(134792207075973/2500000000000000000 : ℝ) ≤ ((22480748677902546467/22485000000000000000 : ℝ)+2*(436528518349/449700000000000 : ℝ)*(10987/100000 : ℝ))^(4557/1024 : ℝ) := by
    rw [show (22480748677902546467/22485000000000000000 : ℝ)+2*(436528518349/449700000000000 : ℝ)*(10987/100000 : ℝ)=(500012115115269/500000000000000 : ℝ) by norm_num, show 1+2*(134792207075973/2500000000000000000 : ℝ)=(1250134792207075973/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4964229413724081/20000000000000000000 : ℝ)+(134792207075973/2500000000000000000 : ℝ) ≤ ((22480748677902546467/22485000000000000000 : ℝ)+(436528518349/449700000000000 : ℝ)*((3871/25000 : ℝ)+(10987/100000 : ℝ)))^(4557/1024 : ℝ) := by
    rw [show (22480748677902546467/22485000000000000000 : ℝ)+(436528518349/449700000000000 : ℝ)*((3871/25000 : ℝ)+(10987/100000 : ℝ))=(10000678830823729/10000000000000000 : ℝ) by norm_num, show 1+(4964229413724081/20000000000000000000 : ℝ)+(134792207075973/2500000000000000000 : ℝ)=(4001208513414066373/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4964229413724081/20000000000000000000 : ℝ) ≤ ((22480748677902546467/22485000000000000000 : ℝ)+2*(436528518349/449700000000000 : ℝ)*(3871/25000 : ℝ))^(4557/1024 : ℝ) := by
    rw [show (22480748677902546467/22485000000000000000 : ℝ)+2*(436528518349/449700000000000 : ℝ)*(3871/25000 : ℝ)=(5000557679671039/5000000000000000 : ℝ) by norm_num, show 1+2*(4964229413724081/20000000000000000000 : ℝ)=(10004964229413724081/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22480748677902546467/22485000000000000000 : ℝ)*(X 1 0+X 2 0)+(436528518349/449700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (10987/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (22480748677902546467/22485000000000000000 : ℝ)) (alpha := (436528518349/449700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22480748677902546467/22485000000000000000 : ℝ)*(X 0 1+X 2 1)+(436528518349/449700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (10987/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (22480748677902546467/22485000000000000000 : ℝ)) (alpha := (436528518349/449700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22480748677902546467/22485000000000000000 : ℝ)*(X 0 2+X 1 2)+(436528518349/449700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4557/1024 : ℝ)) (lo := (10987/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (22480748677902546467/22485000000000000000 : ℝ)) (alpha := (436528518349/449700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-81500871/500000000 : ℝ)*X 0 0+(5400782481/10000000000 : ℝ)*X 0 1+(216031267/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((82359037/156250000 : ℝ)*X 1 0+(-362042381/2000000000 : ℝ)*X 1 1+(1080156563/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1317744569/2500000000 : ℝ)*X 2 0+(5400782909/10000000000 : ℝ)*X 2 1+(-18102119/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2231618679/5000000000 : ℝ)*X 0 0+(4166751511/10000000000 : ℝ)*X 0 1+(4166751397/10000000000 : ℝ)*X 0 2+(2231618679/5000000000 : ℝ)*X 1 0+(4166751511/10000000000 : ℝ)*X 1 1+(4166751397/10000000000 : ℝ)*X 1 2+(2231618679/5000000000 : ℝ)*X 2 0+(4166751511/10000000000 : ℝ)*X 2 1+(4166751397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1028013173/5000000000 : ℝ)*X 0 0+(1048837797/2000000000 : ℝ)*X 0 1+(5244188843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1344960983/2500000000 : ℝ)*X 1 0+(-1875084607/10000000000 : ℝ)*X 1 1+(1311047207/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5379844107/10000000000 : ℝ)*X 2 0+(5244188767/10000000000 : ℝ)*X 2 1+(-1875084451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2028131317/5000000000 : ℝ)*X 0 0+(136565837/312500000 : ℝ)*X 0 1+(4370107031/10000000000 : ℝ)*X 0 2+(2028131317/5000000000 : ℝ)*X 1 0+(136565837/312500000 : ℝ)*X 1 1+(4370107031/10000000000 : ℝ)*X 1 2+(2028131317/5000000000 : ℝ)*X 2 0+(136565837/312500000 : ℝ)*X 2 1+(4370107031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-122869003/625000000 : ℝ)*X 0 0+(320892361/625000000 : ℝ)*X 0 1+(1084235621/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((105135891/200000000 : ℝ)*X 1 0+(-1801520919/10000000000 : ℝ)*X 1 1+(5421178151/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2628397317/5000000000 : ℝ)*X 2 0+(5421177963/10000000000 : ℝ)*X 2 1+(-1801521063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((180603757/400000000 : ℝ)*X 0 0+(4140232879/10000000000 : ℝ)*X 0 1+(4140232829/10000000000 : ℝ)*X 0 2+(180603757/400000000 : ℝ)*X 1 0+(4140232879/10000000000 : ℝ)*X 1 1+(4140232829/10000000000 : ℝ)*X 1 2+(180603757/400000000 : ℝ)*X 2 0+(4140232879/10000000000 : ℝ)*X 2 1+(4140232829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-859994611/5000000000 : ℝ)*X 0 0+(55072227/100000000 : ℝ)*X 0 1+(2614574813/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5390299677/10000000000 : ℝ)*X 1 0+(-188113931/1000000000 : ℝ)*X 1 1+(65364367/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1347574939/2500000000 : ℝ)*X 2 0+(2614574781/5000000000 : ℝ)*X 2 1+(-188113893/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((50203933/125000000 : ℝ)*X 0 0+(4389614079/10000000000 : ℝ)*X 0 1+(4389613477/10000000000 : ℝ)*X 0 2+(50203933/125000000 : ℝ)*X 1 0+(4389614079/10000000000 : ℝ)*X 1 1+(4389613477/10000000000 : ℝ)*X 1 2+(50203933/125000000 : ℝ)*X 2 0+(4389614079/10000000000 : ℝ)*X 2 1+(4389613477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1531_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31883/50000 : ℝ) ≤ (-29869050235491260662235415311997/46843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65652967/100000000000000 : ℝ)*(upper0) + (245257/500000000000 : ℝ)*(lower2) + (21997539/100000000000000 : ℝ)*(upper4) + (7943459/100000000000000 : ℝ)*(upper5) + (281412176112303/12500000000000 : ℝ)*(major0) + (281412176112303/12500000000000 : ℝ)*(major1) + (281412176112303/12500000000000 : ℝ)*(major2) + (362226991/25000000000000 : ℝ)*(sp1) + (689925487/100000000000000 : ℝ)*(sp3) + (3158588751205479/100000000000000 : ℝ)*(sp4) + (3158588316547919/100000000000000 : ℝ)*(sp5) + (3158589765455883/100000000000000 : ℝ)*(sp6) + (136525874550499/10000000000000 : ℝ)*(sp7) + (253562601/25000000000000 : ℝ)*(sp8) + (341314858857619/25000000000000 : ℝ)*(f.failure) + (3158589765455883/100000000000000 : ℝ)*(f.sum) + (397717548411/58554687500000000000000000 : ℝ)*base66 + (570228462373088833/93687500000000000000000000000000 : ℝ)*base68 + (469967089441213833/93687500000000000000000000000000 : ℝ)*base70 + (652355293064963833/93687500000000000000000000000000 : ℝ)*base72 + (2502126810547/1873750000000000000000000000 : ℝ)*base74 + (274142636324026333/93687500000000000000000000000000 : ℝ)*base76 + (805977611832401333/93687500000000000000000000000000 : ℝ)*base78 + (501180394689213833/93687500000000000000000000000000 : ℝ)*base80 + (3111743938007/1873750000000000000000000000 : ℝ)*base82 + (2286779/312500000000000000000 : ℝ)*base90 + (2286779/312500000000000000000 : ℝ)*base92 + (2286779/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58717/100000 : ℝ) ≤ (27506520487248176784040582932681/46843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116594163/100000000000000 : ℝ)*(upper0) + (95452399/50000000000000 : ℝ)*(upper3) + (4419731/6250000000000 : ℝ)*(upper4) + (291105740015093/12500000000000 : ℝ)*(major0) + (291105740015093/12500000000000 : ℝ)*(major1) + (291105740015093/12500000000000 : ℝ)*(major2) + (1612914460873181/50000000000000 : ℝ)*(sp0) + (1612910126029799/50000000000000 : ℝ)*(sp1) + (3225811030336957/100000000000000 : ℝ)*(sp2) + (1412283365132869/100000000000000 : ℝ)*(sp3) + (2747649177/25000000000000 : ℝ)*(sp5) + (404246387/2000000000000 : ℝ)*(sp6) + (464181989/20000000000000 : ℝ)*(sp8) + (798255673/20000000000000 : ℝ)*(sp11) + (706143678205617/50000000000000 : ℝ)*(f.failure) + (806457810664077/25000000000000 : ℝ)*(f.sum) + (28002069785939/22485000000000000000000000000 : ℝ)*base66 + (1275389847900323569/281062500000000000000000000000000 : ℝ)*base68 + (775109507903386069/281062500000000000000000000000000 : ℝ)*base70 + (545934413439238931/281062500000000000000000000000000 : ℝ)*base71 + (46921064487281/5621250000000000000000000000 : ℝ)*base74 + (353885946006426431/281062500000000000000000000000000 : ℝ)*base75 + (608885254374136069/281062500000000000000000000000000 : ℝ)*base78 + (5670488648883886069/281062500000000000000000000000000 : ℝ)*base80 + (18324180090769/5621250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/50000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3420503/625000000000000000000 : ℝ)*base89 + (3420503/625000000000000000000 : ℝ)*base91 + (3420503/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80521/100000 : ℝ) ≤ (150880854908352878584160115388047/187375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3733731/25000000000000 : ℝ)*(upper2) + (22568539/100000000000000 : ℝ)*(lower3) + (1665971/3125000000000 : ℝ)*(lower5) + (1260211928793753/50000000000000 : ℝ)*(major0) + (1260211928793753/50000000000000 : ℝ)*(major1) + (1260211928793753/50000000000000 : ℝ)*(major2) + (89927121711/100000000000000 : ℝ)*(sp1) + (58756087451/100000000000000 : ℝ)*(sp2) + (5796377619/100000000000000 : ℝ)*(sp4) + (174276607999969/5000000000000 : ℝ)*(sp8) + (3485450227767843/100000000000000 : ℝ)*(sp9) + (435685174850263/12500000000000 : ℝ)*(sp10) + (1528466403085829/100000000000000 : ℝ)*(sp11) + (439702511/20000000000000 : ℝ)*(sp12) + (1528466403085829/100000000000000 : ℝ)*(f.failure) + (1742770077444777/50000000000000 : ℝ)*(f.sum) + (16011309372703/7495000000000000000000000000 : ℝ)*base65 + (3517812371540390217/374750000000000000000000000000000 : ℝ)*base67 + (2598123930440890217/374750000000000000000000000000000 : ℝ)*base69 + (3352279174249640217/374750000000000000000000000000000 : ℝ)*base71 + (9138182129293/7495000000000000000000000000 : ℝ)*base73 + (5080707541468640217/374750000000000000000000000000000 : ℝ)*base75 + (3209678886778140217/374750000000000000000000000000000 : ℝ)*base77 + (3002941466794390217/374750000000000000000000000000000 : ℝ)*base79 + (11520303384357/7495000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (9839389/1250000000000000000000 : ℝ)*base90 + (9839389/1250000000000000000000 : ℝ)*base92 + (9839389/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-86123/100000 : ℝ) ≤ (-161368479169925794720207031625483/187375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (152444963/100000000000000 : ℝ)*(lower2) + (22270173/25000000000000 : ℝ)*(upper3) + (60455957/100000000000000 : ℝ)*(upper5) + (1279978165524717/50000000000000 : ℝ)*(major0) + (1279978165524717/50000000000000 : ℝ)*(major1) + (1279978165524717/50000000000000 : ℝ)*(major2) + (5107510271/100000000000000 : ℝ)*(sp0) + (181123632627/100000000000000 : ℝ)*(sp5) + (7811937981/12500000000000 : ℝ)*(sp6) + (10734542899/20000000000000 : ℝ)*(sp7) + (1798087125384661/50000000000000 : ℝ)*(sp12) + (1797999117323483/50000000000000 : ℝ)*(sp13) + (56189325980871/1562500000000 : ℝ)*(sp14) + (776193249323337/50000000000000 : ℝ)*(sp15) + (1552440171361169/100000000000000 : ℝ)*(f.failure) + (449522419784949/12500000000000 : ℝ)*(f.sum) + (1673095451063/1873750000000000000000000000 : ℝ)*base65 + (4259994843225358387/374750000000000000000000000000000 : ℝ)*base68 + (6101654349784608387/374750000000000000000000000000000 : ℝ)*base70 + (4852458650985608387/374750000000000000000000000000000 : ℝ)*base72 + (39512744033707/7495000000000000000000000000 : ℝ)*base73 + (4053598913054858387/374750000000000000000000000000000 : ℝ)*base76 + (4036456585522108387/374750000000000000000000000000000 : ℝ)*base78 + (3436417183652108387/374750000000000000000000000000000 : ℝ)*base80 + (11506524415303/7495000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (9087671/1250000000000000000000 : ℝ)*base89 + (9087671/1250000000000000000000 : ℝ)*base91 + (9087671/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1531_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31883/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58717/100000 : ℝ) else (80521/100000 : ℝ) ≤ X j i ∧ X j i ≤ (86123/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1531_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1531_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31883/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58717/100000 : ℝ) else (80521/100000 : ℝ) ≤ X j i ∧ X j i ≤ (86123/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1531_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1531_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4557/1024 : ℝ) ≤ p) (hpb : p ≤ (4559/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20612359/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10987/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31883/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58717/100000 : ℝ) else (80521/100000 : ℝ) ≤ X j i ∧ X j i ≤ (86123/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1531_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

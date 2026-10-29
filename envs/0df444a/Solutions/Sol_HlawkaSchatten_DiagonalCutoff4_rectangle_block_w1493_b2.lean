-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1493_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:46.98384+00:00
-- url     : https://prove2.me/submissions/7167fe4e-5ec3-4b3a-9ed2-d168e5792316

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
theorem support_rectangle_w1493_s6_0 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-29632117/156250000 : ℝ)*x 0 + (5435717127/10000000000 : ℝ)*x 1 + (5216616807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29632117/156250000 : ℝ)^4483 ≤ (11592718483617/100000000000000 : ℝ)^3459 := by
    have hnat : (29632117 : ℕ)^4483*100000000000000^3459 ≤ 11592718483617^3459*156250000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29632117 156250000 11592718483617 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435717127/10000000000 : ℝ)^4483 ≤ (709091847143/1562500000000 : ℝ)^3459 := by
    have hnat : (5435717127 : ℕ)^4483*1562500000000^3459 ≤ 709091847143^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435717127 10000000000 709091847143 1562500000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216616807/10000000000 : ℝ)^4483 ≤ (10756350821941/25000000000000 : ℝ)^3459 := by
    have hnat : (5216616807 : ℕ)^4483*25000000000000^3459 ≤ 10756350821941^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216616807 10000000000 10756350821941 25000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-29632117/156250000 : ℝ), (5435717127/10000000000 : ℝ), (5216616807/10000000000 : ℝ)] ![(11592718483617/100000000000000 : ℝ), (709091847143/1562500000000 : ℝ), (10756350821941/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-29632117/156250000 : ℝ)|^4483 ≤ (11592718483617/100000000000000 : ℝ)^3459
        have hw : |(-29632117/156250000 : ℝ)|=(29632117/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435717127/10000000000 : ℝ)|^4483 ≤ (709091847143/1562500000000 : ℝ)^3459
        have hw : |(5435717127/10000000000 : ℝ)|=(5435717127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216616807/10000000000 : ℝ)|^4483 ≤ (10756350821941/25000000000000 : ℝ)^3459
        have hw : |(5216616807/10000000000 : ℝ)|=(5216616807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s6_1 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676313059/5000000000 : ℝ)*x 0 + (-2008712163/10000000000 : ℝ)*x 1 + (1043323363/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676313059/5000000000 : ℝ)^4483 ≤ (22242420456831/50000000000000 : ℝ)^3459 := by
    have hnat : (2676313059 : ℕ)^4483*50000000000000^3459 ≤ 22242420456831^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676313059 5000000000 22242420456831 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008712163/10000000000 : ℝ)^4483 ≤ (12489755697119/100000000000000 : ℝ)^3459 := by
    have hnat : (2008712163 : ℕ)^4483*100000000000000^3459 ≤ 12489755697119^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008712163 10000000000 12489755697119 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043323363/2000000000 : ℝ)^4483 ≤ (43025403373279/100000000000000 : ℝ)^3459 := by
    have hnat : (1043323363 : ℕ)^4483*100000000000000^3459 ≤ 43025403373279^3459*2000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043323363 2000000000 43025403373279 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676313059/5000000000 : ℝ), (-2008712163/10000000000 : ℝ), (1043323363/2000000000 : ℝ)] ![(22242420456831/50000000000000 : ℝ), (12489755697119/100000000000000 : ℝ), (43025403373279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676313059/5000000000 : ℝ)|^4483 ≤ (22242420456831/50000000000000 : ℝ)^3459
        have hw : |(2676313059/5000000000 : ℝ)|=(2676313059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2008712163/10000000000 : ℝ)|^4483 ≤ (12489755697119/100000000000000 : ℝ)^3459
        have hw : |(-2008712163/10000000000 : ℝ)|=(2008712163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043323363/2000000000 : ℝ)|^4483 ≤ (43025403373279/100000000000000 : ℝ)^3459
        have hw : |(1043323363/2000000000 : ℝ)|=(1043323363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s6_2 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352626121/10000000000 : ℝ)*x 0 + (2608308399/5000000000 : ℝ)*x 1 + (-2008712181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352626121/10000000000 : ℝ)^4483 ≤ (1779393637839/4000000000000 : ℝ)^3459 := by
    have hnat : (5352626121 : ℕ)^4483*4000000000000^3459 ≤ 1779393637839^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352626121 10000000000 1779393637839 4000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608308399/5000000000 : ℝ)^4483 ≤ (43025403191559/100000000000000 : ℝ)^3459 := by
    have hnat : (2608308399 : ℕ)^4483*100000000000000^3459 ≤ 43025403191559^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608308399 5000000000 43025403191559 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008712181/10000000000 : ℝ)^4483 ≤ (3122438960543/25000000000000 : ℝ)^3459 := by
    have hnat : (2008712181 : ℕ)^4483*25000000000000^3459 ≤ 3122438960543^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008712181 10000000000 3122438960543 25000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352626121/10000000000 : ℝ), (2608308399/5000000000 : ℝ), (-2008712181/10000000000 : ℝ)] ![(1779393637839/4000000000000 : ℝ), (43025403191559/100000000000000 : ℝ), (3122438960543/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352626121/10000000000 : ℝ)|^4483 ≤ (1779393637839/4000000000000 : ℝ)^3459
        have hw : |(5352626121/10000000000 : ℝ)|=(5352626121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608308399/5000000000 : ℝ)|^4483 ≤ (43025403191559/100000000000000 : ℝ)^3459
        have hw : |(2608308399/5000000000 : ℝ)|=(2608308399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2008712181/10000000000 : ℝ)|^4483 ≤ (3122438960543/25000000000000 : ℝ)^3459
        have hw : |(-2008712181/10000000000 : ℝ)|=(2008712181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s6_3 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (855740613/2000000000 : ℝ)*x 0 + (4039666173/10000000000 : ℝ)*x 1 + (4529850433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855740613/2000000000 : ℝ)^4483 ≤ (8319669165711/25000000000000 : ℝ)^3459 := by
    have hnat : (855740613 : ℕ)^4483*25000000000000^3459 ≤ 8319669165711^3459*2000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855740613 2000000000 8319669165711 25000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4039666173/10000000000 : ℝ)^4483 ≤ (386116423241/1250000000000 : ℝ)^3459 := by
    have hnat : (4039666173 : ℕ)^4483*1250000000000^3459 ≤ 386116423241^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039666173 10000000000 386116423241 1250000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4529850433/10000000000 : ℝ)^4483 ≤ (2239500590913/6250000000000 : ℝ)^3459 := by
    have hnat : (4529850433 : ℕ)^4483*6250000000000^3459 ≤ 2239500590913^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529850433 10000000000 2239500590913 6250000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855740613/2000000000 : ℝ), (4039666173/10000000000 : ℝ), (4529850433/10000000000 : ℝ)] ![(8319669165711/25000000000000 : ℝ), (386116423241/1250000000000 : ℝ), (2239500590913/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855740613/2000000000 : ℝ)|^4483 ≤ (8319669165711/25000000000000 : ℝ)^3459
        have hw : |(855740613/2000000000 : ℝ)|=(855740613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4039666173/10000000000 : ℝ)|^4483 ≤ (386116423241/1250000000000 : ℝ)^3459
        have hw : |(4039666173/10000000000 : ℝ)|=(4039666173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4529850433/10000000000 : ℝ)|^4483 ≤ (2239500590913/6250000000000 : ℝ)^3459
        have hw : |(4529850433/10000000000 : ℝ)|=(4529850433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s6_4 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-189648527/1000000000 : ℝ)*x 0 + (2608870219/5000000000 : ℝ)*x 1 + (2717292611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (189648527/1000000000 : ℝ)^4483 ≤ (11592954431281/100000000000000 : ℝ)^3459 := by
    have hnat : (189648527 : ℕ)^4483*100000000000000^3459 ≤ 11592954431281^3459*1000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189648527 1000000000 11592954431281 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608870219/5000000000 : ℝ)^4483 ≤ (1721496585429/4000000000000 : ℝ)^3459 := by
    have hnat : (2608870219 : ℕ)^4483*4000000000000^3459 ≤ 1721496585429^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608870219 5000000000 1721496585429 4000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717292611/5000000000 : ℝ)^4483 ≤ (22684815458153/50000000000000 : ℝ)^3459 := by
    have hnat : (2717292611 : ℕ)^4483*50000000000000^3459 ≤ 22684815458153^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717292611 5000000000 22684815458153 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-189648527/1000000000 : ℝ), (2608870219/5000000000 : ℝ), (2717292611/5000000000 : ℝ)] ![(11592954431281/100000000000000 : ℝ), (1721496585429/4000000000000 : ℝ), (22684815458153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-189648527/1000000000 : ℝ)|^4483 ≤ (11592954431281/100000000000000 : ℝ)^3459
        have hw : |(-189648527/1000000000 : ℝ)|=(189648527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608870219/5000000000 : ℝ)|^4483 ≤ (1721496585429/4000000000000 : ℝ)^3459
        have hw : |(2608870219/5000000000 : ℝ)|=(2608870219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717292611/5000000000 : ℝ)|^4483 ≤ (22684815458153/50000000000000 : ℝ)^3459
        have hw : |(2717292611/5000000000 : ℝ)|=(2717292611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s6_5 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295280819/10000000000 : ℝ)*x 0 + (-447685939/2500000000 : ℝ)*x 1 + (2717292611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295280819/10000000000 : ℝ)^4483 ≤ (43868146328287/100000000000000 : ℝ)^3459 := by
    have hnat : (5295280819 : ℕ)^4483*100000000000000^3459 ≤ 43868146328287^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295280819 10000000000 43868146328287 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447685939/2500000000 : ℝ)^4483 ≤ (10762222745309/100000000000000 : ℝ)^3459 := by
    have hnat : (447685939 : ℕ)^4483*100000000000000^3459 ≤ 10762222745309^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447685939 2500000000 10762222745309 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717292611/5000000000 : ℝ)^4483 ≤ (22684815458153/50000000000000 : ℝ)^3459 := by
    have hnat : (2717292611 : ℕ)^4483*50000000000000^3459 ≤ 22684815458153^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717292611 5000000000 22684815458153 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295280819/10000000000 : ℝ), (-447685939/2500000000 : ℝ), (2717292611/5000000000 : ℝ)] ![(43868146328287/100000000000000 : ℝ), (10762222745309/100000000000000 : ℝ), (22684815458153/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295280819/10000000000 : ℝ)|^4483 ≤ (43868146328287/100000000000000 : ℝ)^3459
        have hw : |(5295280819/10000000000 : ℝ)|=(5295280819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447685939/2500000000 : ℝ)|^4483 ≤ (10762222745309/100000000000000 : ℝ)^3459
        have hw : |(-447685939/2500000000 : ℝ)|=(447685939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717292611/5000000000 : ℝ)|^4483 ≤ (22684815458153/50000000000000 : ℝ)^3459
        have hw : |(2717292611/5000000000 : ℝ)|=(2717292611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s6_6 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295280819/10000000000 : ℝ)*x 0 + (2717292611/5000000000 : ℝ)*x 1 + (-447685939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295280819/10000000000 : ℝ)^4483 ≤ (43868146328287/100000000000000 : ℝ)^3459 := by
    have hnat : (5295280819 : ℕ)^4483*100000000000000^3459 ≤ 43868146328287^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295280819 10000000000 43868146328287 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717292611/5000000000 : ℝ)^4483 ≤ (22684815458153/50000000000000 : ℝ)^3459 := by
    have hnat : (2717292611 : ℕ)^4483*50000000000000^3459 ≤ 22684815458153^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717292611 5000000000 22684815458153 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447685939/2500000000 : ℝ)^4483 ≤ (10762222745309/100000000000000 : ℝ)^3459 := by
    have hnat : (447685939 : ℕ)^4483*100000000000000^3459 ≤ 10762222745309^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447685939 2500000000 10762222745309 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295280819/10000000000 : ℝ), (2717292611/5000000000 : ℝ), (-447685939/2500000000 : ℝ)] ![(43868146328287/100000000000000 : ℝ), (22684815458153/50000000000000 : ℝ), (10762222745309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295280819/10000000000 : ℝ)|^4483 ≤ (43868146328287/100000000000000 : ℝ)^3459
        have hw : |(5295280819/10000000000 : ℝ)|=(5295280819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717292611/5000000000 : ℝ)|^4483 ≤ (22684815458153/50000000000000 : ℝ)^3459
        have hw : |(2717292611/5000000000 : ℝ)|=(2717292611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-447685939/2500000000 : ℝ)|^4483 ≤ (10762222745309/100000000000000 : ℝ)^3459
        have hw : |(-447685939/2500000000 : ℝ)|=(447685939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s6_7 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267423107/625000000 : ℝ)*x 0 + (4527336527/10000000000 : ℝ)*x 1 + (2021099267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267423107/625000000 : ℝ)^4483 ≤ (33279348484011/100000000000000 : ℝ)^3459 := by
    have hnat : (267423107 : ℕ)^4483*100000000000000^3459 ≤ 33279348484011^3459*625000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267423107 625000000 33279348484011 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4527336527/10000000000 : ℝ)^4483 ≤ (3580623919277/10000000000000 : ℝ)^3459 := by
    have hnat : (4527336527 : ℕ)^4483*10000000000000^3459 ≤ 3580623919277^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527336527 10000000000 3580623919277 10000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2021099267/5000000000 : ℝ)^4483 ≤ (15457206153649/50000000000000 : ℝ)^3459 := by
    have hnat : (2021099267 : ℕ)^4483*50000000000000^3459 ≤ 15457206153649^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021099267 5000000000 15457206153649 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267423107/625000000 : ℝ), (4527336527/10000000000 : ℝ), (2021099267/5000000000 : ℝ)] ![(33279348484011/100000000000000 : ℝ), (3580623919277/10000000000000 : ℝ), (15457206153649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267423107/625000000 : ℝ)|^4483 ≤ (33279348484011/100000000000000 : ℝ)^3459
        have hw : |(267423107/625000000 : ℝ)|=(267423107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4527336527/10000000000 : ℝ)|^4483 ≤ (3580623919277/10000000000000 : ℝ)^3459
        have hw : |(4527336527/10000000000 : ℝ)|=(4527336527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2021099267/5000000000 : ℝ)|^4483 ≤ (15457206153649/50000000000000 : ℝ)^3459
        have hw : |(2021099267/5000000000 : ℝ)|=(2021099267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1493_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10839/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (271/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15479/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10839/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10839/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10839/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10839/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10839/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10839/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10839/100000 : ℝ) ^ (4481/1024 : ℝ) ≤ (2992991147091629/50000000000000000000 : ℝ) := by
    have hpowers : (10839/100000 : ℝ)^4481 ≤ (2992991147091629/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10839 : ℕ)^4481*50000000000000000000^1024 ≤ 2992991147091629^1024*100000^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10839 100000 2992991147091629 50000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10839/100000 : ℝ)) (X := (2992991147091629/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (387/2500 : ℝ) ^ (4481/1024 : ℝ) ≤ (28474538547223477/100000000000000000000 : ℝ) := by
    have hpowers : (387/2500 : ℝ)^4481 ≤ (28474538547223477/100000000000000000000 : ℝ)^1024 := by
      have hnat : (387 : ℕ)^4481*100000000000000000000^1024 ≤ 28474538547223477^1024*2500^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        387 2500 28474538547223477 100000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (387/2500 : ℝ)) (X := (28474538547223477/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002992991147091629/25000000000000000000 : ℝ) ≤ (2500068392800919/2500000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (25002992991147091629/25000000000000000000 : ℝ)^1024 ≤ (2500068392800919/2500000000000000 : ℝ)^4481 := by
      have hnat : (25002992991147091629 : ℕ)^1024*2500000000000000^4481 ≤ 2500068392800919^4481*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002992991147091629 25000000000000000000 2500068392800919 2500000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500068392800919/2500000000000000 : ℝ)) (X := (25002992991147091629/25000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20006892104168281347/20000000000000000000 : ℝ) ≤ (5000393694304747/5000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (20006892104168281347/20000000000000000000 : ℝ)^1024 ≤ (5000393694304747/5000000000000000 : ℝ)^4481 := by
      have hnat : (20006892104168281347 : ℕ)^1024*5000000000000000^4481 ≤ 5000393694304747^4481*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006892104168281347 20000000000000000000 5000393694304747 5000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000393694304747/5000000000000000 : ℝ)) (X := (20006892104168281347/20000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028474538547223477/50000000000000000000 : ℝ) ≤ (625081325375957/625000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (50028474538547223477/50000000000000000000 : ℝ)^1024 ≤ (625081325375957/625000000000000 : ℝ)^4481 := by
      have hnat : (50028474538547223477 : ℕ)^1024*625000000000000^4481 ≤ 625081325375957^4481*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028474538547223477 50000000000000000000 625081325375957 625000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625081325375957/625000000000000 : ℝ)) (X := (50028474538547223477/50000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2992991147091629/50000000000000000000 : ℝ) ≤ ((966669398129852869/966875000000000000 : ℝ)+2*(85636234303/77350000000000 : ℝ)*(10839/100000 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (966669398129852869/966875000000000000 : ℝ)+2*(85636234303/77350000000000 : ℝ)*(10839/100000 : ℝ)=(2500068392800919/2500000000000000 : ℝ) by norm_num, show 1+2*(2992991147091629/50000000000000000000 : ℝ)=(25002992991147091629/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28474538547223477/100000000000000000000 : ℝ)+(2992991147091629/50000000000000000000 : ℝ) ≤ ((966669398129852869/966875000000000000 : ℝ)+(85636234303/77350000000000 : ℝ)*((387/2500 : ℝ)+(10839/100000 : ℝ)))^(4481/1024 : ℝ) := by
    rw [show (966669398129852869/966875000000000000 : ℝ)+(85636234303/77350000000000 : ℝ)*((387/2500 : ℝ)+(10839/100000 : ℝ))=(5000393694304747/5000000000000000 : ℝ) by norm_num, show 1+(28474538547223477/100000000000000000000 : ℝ)+(2992991147091629/50000000000000000000 : ℝ)=(20006892104168281347/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28474538547223477/100000000000000000000 : ℝ) ≤ ((966669398129852869/966875000000000000 : ℝ)+2*(85636234303/77350000000000 : ℝ)*(387/2500 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (966669398129852869/966875000000000000 : ℝ)+2*(85636234303/77350000000000 : ℝ)*(387/2500 : ℝ)=(625081325375957/625000000000000 : ℝ) by norm_num, show 1+2*(28474538547223477/100000000000000000000 : ℝ)=(50028474538547223477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (966669398129852869/966875000000000000 : ℝ)*(X 1 0+X 2 0)+(85636234303/77350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (10839/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (966669398129852869/966875000000000000 : ℝ)) (alpha := (85636234303/77350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (966669398129852869/966875000000000000 : ℝ)*(X 0 1+X 2 1)+(85636234303/77350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (10839/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (966669398129852869/966875000000000000 : ℝ)) (alpha := (85636234303/77350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (966669398129852869/966875000000000000 : ℝ)*(X 0 2+X 1 2)+(85636234303/77350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (10839/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (966669398129852869/966875000000000000 : ℝ)) (alpha := (85636234303/77350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-29632117/156250000 : ℝ)*X 0 0+(5435717127/10000000000 : ℝ)*X 0 1+(5216616807/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676313059/5000000000 : ℝ)*X 1 0+(-2008712163/10000000000 : ℝ)*X 1 1+(1043323363/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352626121/10000000000 : ℝ)*X 2 0+(2608308399/5000000000 : ℝ)*X 2 1+(-2008712181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((855740613/2000000000 : ℝ)*X 0 0+(4039666173/10000000000 : ℝ)*X 0 1+(4529850433/10000000000 : ℝ)*X 0 2+(855740613/2000000000 : ℝ)*X 1 0+(4039666173/10000000000 : ℝ)*X 1 1+(4529850433/10000000000 : ℝ)*X 1 2+(855740613/2000000000 : ℝ)*X 2 0+(4039666173/10000000000 : ℝ)*X 2 1+(4529850433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-189648527/1000000000 : ℝ)*X 0 0+(2608870219/5000000000 : ℝ)*X 0 1+(2717292611/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295280819/10000000000 : ℝ)*X 1 0+(-447685939/2500000000 : ℝ)*X 1 1+(2717292611/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295280819/10000000000 : ℝ)*X 2 0+(2717292611/5000000000 : ℝ)*X 2 1+(-447685939/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((267423107/625000000 : ℝ)*X 0 0+(4527336527/10000000000 : ℝ)*X 0 1+(2021099267/5000000000 : ℝ)*X 0 2+(267423107/625000000 : ℝ)*X 1 0+(4527336527/10000000000 : ℝ)*X 1 1+(2021099267/5000000000 : ℝ)*X 1 2+(267423107/625000000 : ℝ)*X 2 0+(4527336527/10000000000 : ℝ)*X 2 1+(2021099267/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (241885226893038656578281459/24171875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (217979627/12500000000000 : ℝ)*(base19) + (1634046253/100000000000000 : ℝ)*(base23) + (60136143/100000000000000 : ℝ)*(lower2) + (62372641/25000000000000 : ℝ)*(upper3) + (150073403/100000000000000 : ℝ)*(upper5) + (1651062366709037/50000000000000 : ℝ)*(major0) + (1651062366709037/50000000000000 : ℝ)*(major1) + (1651062366709037/50000000000000 : ℝ)*(major2) + (2282073901422339/50000000000000 : ℝ)*(sp0) + (1141043262344711/25000000000000 : ℝ)*(sp1) + (4564173159169607/100000000000000 : ℝ)*(sp2) + (1020030494181593/50000000000000 : ℝ)*(sp3) + (26990371183/100000000000000 : ℝ)*(sp4) + (3337923547/25000000000000 : ℝ)*(sp7) + (1020037170028687/50000000000000 : ℝ)*(f.failure) + (228208739660793/5000000000000 : ℝ)*(f.sum) + (9347375125481/1933750000000000000000000000 : ℝ)*base65 + (279472865040872847/48343750000000000000000000000000 : ℝ)*base68 + (697754118191997847/48343750000000000000000000000000 : ℝ)*base70 + (57268618423877153/48343750000000000000000000000000 : ℝ)*base71 + (5253250094787/3867500000000000000000000000 : ℝ)*base73 + (12428336414997847/48343750000000000000000000000000 : ℝ)*base76 + (297708344839970903/48343750000000000000000000000000 : ℝ)*base77 + (565322696757185347/48343750000000000000000000000000 : ℝ)*base80 + (47787278297461/7735000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (32762207/5000000000000000000000 : ℝ)*base89 + (32762207/5000000000000000000000 : ℝ)*base91 + (32762207/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9295379358382555251309/773500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1976363287/100000000000000 : ℝ)*(base19) + (2145148263/100000000000000 : ℝ)*(base23) + (32715153/5000000000000 : ℝ)*(lower1) + (247988757/100000000000000 : ℝ)*(upper3) + (15259611/20000000000000 : ℝ)*(lower4) + (247505577/100000000000000 : ℝ)*(upper5) + (333640888785647/10000000000000 : ℝ)*(major0) + (333640888785647/10000000000000 : ℝ)*(major1) + (333640888785647/10000000000000 : ℝ)*(major2) + (114031247/5000000000000 : ℝ)*(sp2) + (461156205937793/10000000000000 : ℝ)*(sp4) + (4611560083014643/100000000000000 : ℝ)*(sp5) + (2305778816802363/50000000000000 : ℝ)*(sp6) + (412251063151683/20000000000000 : ℝ)*(sp7) + (412251063151683/20000000000000 : ℝ)*(f.failure) + (461156205937793/10000000000000 : ℝ)*(f.sum) + (288780757913/193375000000000000000000000 : ℝ)*base65 + (17820041579389993/9668750000000000000000000000000 : ℝ)*base67 + (60823211987328757/9668750000000000000000000000000 : ℝ)*base70 + (1706430394217135007/9668750000000000000000000000000 : ℝ)*base72 + (938069392479/309400000000000000000000000 : ℝ)*base74 + (63261123466158743/9668750000000000000000000000000 : ℝ)*base75 + (11397729430878757/9668750000000000000000000000000 : ℝ)*base78 + (172858757693489993/9668750000000000000000000000000 : ℝ)*base79 + (1382841259847/773500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2513363/2000000000000000000000 : ℝ)*base89 + (2513363/2000000000000000000000 : ℝ)*base91 + (2513363/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1493_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10839/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (271/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1493_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1493_s7_0 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1896456319/10000000000 : ℝ)*x 0 + (1087142157/2000000000 : ℝ)*x 1 + (521662261/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1896456319/10000000000 : ℝ)^4483 ≤ (11592725067193/100000000000000 : ℝ)^3459 := by
    have hnat : (1896456319 : ℕ)^4483*100000000000000^3459 ≤ 11592725067193^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896456319 10000000000 11592725067193 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087142157/2000000000 : ℝ)^4483 ≤ (45381809594111/100000000000000 : ℝ)^3459 := by
    have hnat : (1087142157 : ℕ)^4483*100000000000000^3459 ≤ 45381809594111^3459*2000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087142157 2000000000 45381809594111 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521662261/1000000000 : ℝ)^4483 ≤ (21512732659243/50000000000000 : ℝ)^3459 := by
    have hnat : (521662261 : ℕ)^4483*50000000000000^3459 ≤ 21512732659243^3459*1000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521662261 1000000000 21512732659243 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1896456319/10000000000 : ℝ), (1087142157/2000000000 : ℝ), (521662261/1000000000 : ℝ)] ![(11592725067193/100000000000000 : ℝ), (45381809594111/100000000000000 : ℝ), (21512732659243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1896456319/10000000000 : ℝ)|^4483 ≤ (11592725067193/100000000000000 : ℝ)^3459
        have hw : |(-1896456319/10000000000 : ℝ)|=(1896456319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087142157/2000000000 : ℝ)|^4483 ≤ (45381809594111/100000000000000 : ℝ)^3459
        have hw : |(1087142157/2000000000 : ℝ)|=(1087142157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521662261/1000000000 : ℝ)|^4483 ≤ (21512732659243/50000000000000 : ℝ)^3459
        have hw : |(521662261/1000000000 : ℝ)|=(521662261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s7_1 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-237060671/1250000000 : ℝ)*x 0 + (260887321/500000000 : ℝ)*x 1 + (135864481/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (237060671/1250000000 : ℝ)^4483 ≤ (11592955207687/100000000000000 : ℝ)^3459 := by
    have hnat : (237060671 : ℕ)^4483*100000000000000^3459 ≤ 11592955207687^3459*1250000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237060671 1250000000 11592955207687 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260887321/500000000 : ℝ)^4483 ≤ (43037478583931/100000000000000 : ℝ)^3459 := by
    have hnat : (260887321 : ℕ)^4483*100000000000000^3459 ≤ 43037478583931^3459*500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260887321 500000000 43037478583931 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135864481/250000000 : ℝ)^4483 ≤ (45369566192603/100000000000000 : ℝ)^3459 := by
    have hnat : (135864481 : ℕ)^4483*100000000000000^3459 ≤ 45369566192603^3459*250000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135864481 250000000 45369566192603 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-237060671/1250000000 : ℝ), (260887321/500000000 : ℝ), (135864481/250000000 : ℝ)] ![(11592955207687/100000000000000 : ℝ), (43037478583931/100000000000000 : ℝ), (45369566192603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-237060671/1250000000 : ℝ)|^4483 ≤ (11592955207687/100000000000000 : ℝ)^3459
        have hw : |(-237060671/1250000000 : ℝ)|=(237060671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260887321/500000000 : ℝ)|^4483 ≤ (43037478583931/100000000000000 : ℝ)^3459
        have hw : |(260887321/500000000 : ℝ)|=(260887321/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135864481/250000000 : ℝ)|^4483 ≤ (45369566192603/100000000000000 : ℝ)^3459
        have hw : |(135864481/250000000 : ℝ)|=(135864481/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s7_2 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295281099/10000000000 : ℝ)*x 0 + (-447687579/2500000000 : ℝ)*x 1 + (2717290111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295281099/10000000000 : ℝ)^4483 ≤ (5483518666827/12500000000000 : ℝ)^3459 := by
    have hnat : (5295281099 : ℕ)^4483*12500000000000^3459 ≤ 5483518666827^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295281099 10000000000 5483518666827 12500000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447687579/2500000000 : ℝ)^4483 ≤ (2152454768353/20000000000000 : ℝ)^3459 := by
    have hnat : (447687579 : ℕ)^4483*20000000000000^3459 ≤ 2152454768353^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447687579 2500000000 2152454768353 20000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717290111/5000000000 : ℝ)^4483 ≤ (45369576817589/100000000000000 : ℝ)^3459 := by
    have hnat : (2717290111 : ℕ)^4483*100000000000000^3459 ≤ 45369576817589^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717290111 5000000000 45369576817589 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295281099/10000000000 : ℝ), (-447687579/2500000000 : ℝ), (2717290111/5000000000 : ℝ)] ![(5483518666827/12500000000000 : ℝ), (2152454768353/20000000000000 : ℝ), (45369576817589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295281099/10000000000 : ℝ)|^4483 ≤ (5483518666827/12500000000000 : ℝ)^3459
        have hw : |(5295281099/10000000000 : ℝ)|=(5295281099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447687579/2500000000 : ℝ)|^4483 ≤ (2152454768353/20000000000000 : ℝ)^3459
        have hw : |(-447687579/2500000000 : ℝ)|=(447687579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717290111/5000000000 : ℝ)|^4483 ≤ (45369576817589/100000000000000 : ℝ)^3459
        have hw : |(2717290111/5000000000 : ℝ)|=(2717290111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s7_3 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529528119/1000000000 : ℝ)*x 0 + (2717290041/5000000000 : ℝ)*x 1 + (-111921899/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529528119/1000000000 : ℝ)^4483 ≤ (43868150311673/100000000000000 : ℝ)^3459 := by
    have hnat : (529528119 : ℕ)^4483*100000000000000^3459 ≤ 43868150311673^3459*1000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529528119 1000000000 43868150311673 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717290041/5000000000 : ℝ)^4483 ≤ (22684787651413/50000000000000 : ℝ)^3459 := by
    have hnat : (2717290041 : ℕ)^4483*50000000000000^3459 ≤ 22684787651413^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717290041 5000000000 22684787651413 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111921899/625000000 : ℝ)^4483 ≤ (336321074107/3125000000000 : ℝ)^3459 := by
    have hnat : (111921899 : ℕ)^4483*3125000000000^3459 ≤ 336321074107^3459*625000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111921899 625000000 336321074107 3125000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529528119/1000000000 : ℝ), (2717290041/5000000000 : ℝ), (-111921899/625000000 : ℝ)] ![(43868150311673/100000000000000 : ℝ), (22684787651413/50000000000000 : ℝ), (336321074107/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529528119/1000000000 : ℝ)|^4483 ≤ (43868150311673/100000000000000 : ℝ)^3459
        have hw : |(529528119/1000000000 : ℝ)|=(529528119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717290041/5000000000 : ℝ)|^4483 ≤ (22684787651413/50000000000000 : ℝ)^3459
        have hw : |(2717290041/5000000000 : ℝ)|=(2717290041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-111921899/625000000 : ℝ)|^4483 ≤ (336321074107/3125000000000 : ℝ)^3459
        have hw : |(-111921899/625000000 : ℝ)|=(111921899/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s7_4 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4278772103/10000000000 : ℝ)*x 0 + (4527321497/10000000000 : ℝ)*x 1 + (2021105823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278772103/10000000000 : ℝ)^4483 ≤ (6655874517209/20000000000000 : ℝ)^3459 := by
    have hnat : (4278772103 : ℕ)^4483*20000000000000^3459 ≤ 6655874517209^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278772103 10000000000 6655874517209 20000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4527321497/10000000000 : ℝ)^4483 ≤ (35806085131713/100000000000000 : ℝ)^3459 := by
    have hnat : (4527321497 : ℕ)^4483*100000000000000^3459 ≤ 35806085131713^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527321497 10000000000 35806085131713 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2021105823/5000000000 : ℝ)^4483 ≤ (3864317784197/12500000000000 : ℝ)^3459 := by
    have hnat : (2021105823 : ℕ)^4483*12500000000000^3459 ≤ 3864317784197^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021105823 5000000000 3864317784197 12500000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278772103/10000000000 : ℝ), (4527321497/10000000000 : ℝ), (2021105823/5000000000 : ℝ)] ![(6655874517209/20000000000000 : ℝ), (35806085131713/100000000000000 : ℝ), (3864317784197/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278772103/10000000000 : ℝ)|^4483 ≤ (6655874517209/20000000000000 : ℝ)^3459
        have hw : |(4278772103/10000000000 : ℝ)|=(4278772103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4527321497/10000000000 : ℝ)|^4483 ≤ (35806085131713/100000000000000 : ℝ)^3459
        have hw : |(4527321497/10000000000 : ℝ)|=(4527321497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2021105823/5000000000 : ℝ)|^4483 ≤ (3864317784197/12500000000000 : ℝ)^3459
        have hw : |(2021105823/5000000000 : ℝ)|=(2021105823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1493_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (271/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (271/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7739/50000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (271/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (271/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (271/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (271/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (271/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (271/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (271/2500 : ℝ) ^ (4481/1024 : ℝ) ≤ (5988399361981741/100000000000000000000 : ℝ) := by
    have hpowers : (271/2500 : ℝ)^4481 ≤ (5988399361981741/100000000000000000000 : ℝ)^1024 := by
      have hnat : (271 : ℕ)^4481*100000000000000000000^1024 ≤ 5988399361981741^1024*2500^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        271 2500 5988399361981741 100000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (271/2500 : ℝ)) (X := (5988399361981741/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15479/100000 : ℝ) ^ (4481/1024 : ℝ) ≤ (14233245038249981/50000000000000000000 : ℝ) := by
    have hpowers : (15479/100000 : ℝ)^4481 ≤ (14233245038249981/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15479 : ℕ)^4481*50000000000000000000^1024 ≤ 14233245038249981^1024*100000^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15479 100000 14233245038249981 50000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15479/100000 : ℝ)) (X := (14233245038249981/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005988399361981741/50000000000000000000 : ℝ) ≤ (10000273681663341/10000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (50005988399361981741/50000000000000000000 : ℝ)^1024 ≤ (10000273681663341/10000000000000000 : ℝ)^4481 := by
      have hnat : (50005988399361981741 : ℕ)^1024*10000000000000000^4481 ≤ 10000273681663341^4481*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005988399361981741 50000000000000000000 10000273681663341 10000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000273681663341/10000000000000000 : ℝ)) (X := (50005988399361981741/50000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034454889438481703/100000000000000000000 : ℝ) ≤ (5000393629977319/5000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (100034454889438481703/100000000000000000000 : ℝ)^1024 ≤ (5000393629977319/5000000000000000 : ℝ)^4481 := by
      have hnat : (100034454889438481703 : ℕ)^1024*5000000000000000^4481 ≤ 5000393629977319^4481*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034454889438481703 100000000000000000000 5000393629977319 5000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000393629977319/5000000000000000 : ℝ)) (X := (100034454889438481703/100000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014233245038249981/25000000000000000000 : ℝ) ≤ (2000260167649187/2000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (25014233245038249981/25000000000000000000 : ℝ)^1024 ≤ (2000260167649187/2000000000000000 : ℝ)^4481 := by
      have hnat : (25014233245038249981 : ℕ)^1024*2000000000000000^4481 ≤ 2000260167649187^4481*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014233245038249981 25000000000000000000 2000260167649187 2000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000260167649187/2000000000000000 : ℝ)) (X := (25014233245038249981/25000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5988399361981741/100000000000000000000 : ℝ) ≤ ((46380135231880919939/46390000000000000000 : ℝ)+2*(513578291297/463900000000000 : ℝ)*(271/2500 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (46380135231880919939/46390000000000000000 : ℝ)+2*(513578291297/463900000000000 : ℝ)*(271/2500 : ℝ)=(10000273681663341/10000000000000000 : ℝ) by norm_num, show 1+2*(5988399361981741/100000000000000000000 : ℝ)=(50005988399361981741/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14233245038249981/50000000000000000000 : ℝ)+(5988399361981741/100000000000000000000 : ℝ) ≤ ((46380135231880919939/46390000000000000000 : ℝ)+(513578291297/463900000000000 : ℝ)*((15479/100000 : ℝ)+(271/2500 : ℝ)))^(4481/1024 : ℝ) := by
    rw [show (46380135231880919939/46390000000000000000 : ℝ)+(513578291297/463900000000000 : ℝ)*((15479/100000 : ℝ)+(271/2500 : ℝ))=(5000393629977319/5000000000000000 : ℝ) by norm_num, show 1+(14233245038249981/50000000000000000000 : ℝ)+(5988399361981741/100000000000000000000 : ℝ)=(100034454889438481703/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14233245038249981/50000000000000000000 : ℝ) ≤ ((46380135231880919939/46390000000000000000 : ℝ)+2*(513578291297/463900000000000 : ℝ)*(15479/100000 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (46380135231880919939/46390000000000000000 : ℝ)+2*(513578291297/463900000000000 : ℝ)*(15479/100000 : ℝ)=(2000260167649187/2000000000000000 : ℝ) by norm_num, show 1+2*(14233245038249981/50000000000000000000 : ℝ)=(25014233245038249981/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46380135231880919939/46390000000000000000 : ℝ)*(X 1 0+X 2 0)+(513578291297/463900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (271/2500 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (46380135231880919939/46390000000000000000 : ℝ)) (alpha := (513578291297/463900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46380135231880919939/46390000000000000000 : ℝ)*(X 0 1+X 2 1)+(513578291297/463900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (271/2500 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (46380135231880919939/46390000000000000000 : ℝ)) (alpha := (513578291297/463900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46380135231880919939/46390000000000000000 : ℝ)*(X 0 2+X 1 2)+(513578291297/463900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (271/2500 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (46380135231880919939/46390000000000000000 : ℝ)) (alpha := (513578291297/463900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1896456319/10000000000 : ℝ)*X 0 0+(1087142157/2000000000 : ℝ)*X 0 1+(521662261/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-237060671/1250000000 : ℝ)*X 0 0+(260887321/500000000 : ℝ)*X 0 1+(135864481/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s7_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295281099/10000000000 : ℝ)*X 1 0+(-447687579/2500000000 : ℝ)*X 1 1+(2717290111/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s7_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((529528119/1000000000 : ℝ)*X 2 0+(2717290041/5000000000 : ℝ)*X 2 1+(-111921899/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s7_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4278772103/10000000000 : ℝ)*X 0 0+(4527321497/10000000000 : ℝ)*X 0 1+(2021105823/5000000000 : ℝ)*X 0 2+(4278772103/10000000000 : ℝ)*X 1 0+(4527321497/10000000000 : ℝ)*X 1 1+(2021105823/5000000000 : ℝ)*X 1 2+(4278772103/10000000000 : ℝ)*X 2 0+(4527321497/10000000000 : ℝ)*X 2 1+(2021105823/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s7_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1294064290409838470543681091/579875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (187088497/100000000000000 : ℝ)*(base8) + (912035321/100000000000000 : ℝ)*(base15) + (4446347/5000000000000 : ℝ)*(lower2) + (85915211/100000000000000 : ℝ)*(upper3) + (119011541/25000000000000 : ℝ)*(lower4) + (315964707/100000000000000 : ℝ)*(upper5) + (834152683053641/25000000000000 : ℝ)*(major0) + (834152683053641/25000000000000 : ℝ)*(major1) + (834152683053641/25000000000000 : ℝ)*(major2) + (1239263693/100000000000000 : ℝ)*(sp0) + (4611839947161349/100000000000000 : ℝ)*(sp1) + (2305920230739109/50000000000000 : ℝ)*(sp2) + (4611841373513539/100000000000000 : ℝ)*(sp3) + (1030690008264017/50000000000000 : ℝ)*(sp4) + (1030690008264017/50000000000000 : ℝ)*(f.failure) + (4611841373513539/100000000000000 : ℝ)*(f.sum) + (529981310480077/23195000000000000000000000000 : ℝ)*base66 + (17789973454158102101/1159750000000000000000000000000000 : ℝ)*base68 + (14661061860275352101/1159750000000000000000000000000000 : ℝ)*base70 + (23915356141167852101/1159750000000000000000000000000000 : ℝ)*base72 + (46202217366221/11597500000000000000000000000 : ℝ)*base74 + (16475967283508852101/1159750000000000000000000000000000 : ℝ)*base76 + (14523039384190852101/1159750000000000000000000000000000 : ℝ)*base78 + (8512646820084852101/1159750000000000000000000000000000 : ℝ)*base80 + (73398282433/90605468750000000000000000 : ℝ)*base81 + (61374337/5000000000000000000000 : ℝ)*base89 + (61374337/5000000000000000000000 : ℝ)*base91 + (61374337/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1493_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (271/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (271/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1493_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1493_box_0 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1679370541/10000000000 : ℝ)*x 0 + (5404889733/10000000000 : ℝ)*x 1 + (1080977583/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1679370541/10000000000 : ℝ)^4483 ≤ (1980566522601/20000000000000 : ℝ)^3459 := by
    have hnat : (1679370541 : ℕ)^4483*20000000000000^3459 ≤ 1980566522601^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1679370541 10000000000 1980566522601 20000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404889733/10000000000 : ℝ)^4483 ≤ (45048593502847/100000000000000 : ℝ)^3459 := by
    have hnat : (5404889733 : ℕ)^4483*100000000000000^3459 ≤ 45048593502847^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404889733 10000000000 45048593502847 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080977583/2000000000 : ℝ)^4483 ≤ (2815535866527/6250000000000 : ℝ)^3459 := by
    have hnat : (1080977583 : ℕ)^4483*6250000000000^3459 ≤ 2815535866527^3459*2000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080977583 2000000000 2815535866527 6250000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1679370541/10000000000 : ℝ), (5404889733/10000000000 : ℝ), (1080977583/2000000000 : ℝ)] ![(1980566522601/20000000000000 : ℝ), (45048593502847/100000000000000 : ℝ), (2815535866527/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1679370541/10000000000 : ℝ)|^4483 ≤ (1980566522601/20000000000000 : ℝ)^3459
        have hw : |(-1679370541/10000000000 : ℝ)|=(1679370541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404889733/10000000000 : ℝ)|^4483 ≤ (45048593502847/100000000000000 : ℝ)^3459
        have hw : |(5404889733/10000000000 : ℝ)|=(5404889733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080977583/2000000000 : ℝ)|^4483 ≤ (2815535866527/6250000000000 : ℝ)^3459
        have hw : |(1080977583/2000000000 : ℝ)|=(1080977583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_box_1 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317621397/2500000000 : ℝ)*x 0 + (-466414379/2500000000 : ℝ)*x 1 + (5404888617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317621397/2500000000 : ℝ)^4483 ≤ (43602107408921/100000000000000 : ℝ)^3459 := by
    have hnat : (1317621397 : ℕ)^4483*100000000000000^3459 ≤ 43602107408921^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317621397 2500000000 43602107408921 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466414379/2500000000 : ℝ)^4483 ≤ (11349311126011/100000000000000 : ℝ)^3459 := by
    have hnat : (466414379 : ℕ)^4483*100000000000000^3459 ≤ 11349311126011^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466414379 2500000000 11349311126011 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404888617/10000000000 : ℝ)^4483 ≤ (22524290723791/50000000000000 : ℝ)^3459 := by
    have hnat : (5404888617 : ℕ)^4483*50000000000000^3459 ≤ 22524290723791^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404888617 10000000000 22524290723791 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317621397/2500000000 : ℝ), (-466414379/2500000000 : ℝ), (5404888617/10000000000 : ℝ)] ![(43602107408921/100000000000000 : ℝ), (11349311126011/100000000000000 : ℝ), (22524290723791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317621397/2500000000 : ℝ)|^4483 ≤ (43602107408921/100000000000000 : ℝ)^3459
        have hw : |(1317621397/2500000000 : ℝ)|=(1317621397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-466414379/2500000000 : ℝ)|^4483 ≤ (11349311126011/100000000000000 : ℝ)^3459
        have hw : |(-466414379/2500000000 : ℝ)|=(466414379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404888617/10000000000 : ℝ)|^4483 ≤ (22524290723791/50000000000000 : ℝ)^3459
        have hw : |(5404888617/10000000000 : ℝ)|=(5404888617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_box_2 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635243/5000000 : ℝ)*x 0 + (5404888971/10000000000 : ℝ)*x 1 + (-1865656471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635243/5000000 : ℝ)^4483 ≤ (43602111826377/100000000000000 : ℝ)^3459 := by
    have hnat : (2635243 : ℕ)^4483*100000000000000^3459 ≤ 43602111826377^3459*5000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635243 5000000 43602111826377 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404888971/10000000000 : ℝ)^4483 ≤ (11262146317891/25000000000000 : ℝ)^3459 := by
    have hnat : (5404888971 : ℕ)^4483*25000000000000^3459 ≤ 11262146317891^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404888971 10000000000 11262146317891 25000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1865656471/10000000000 : ℝ)^4483 ≤ (11349302887059/100000000000000 : ℝ)^3459 := by
    have hnat : (1865656471 : ℕ)^4483*100000000000000^3459 ≤ 11349302887059^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865656471 10000000000 11349302887059 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635243/5000000 : ℝ), (5404888971/10000000000 : ℝ), (-1865656471/10000000000 : ℝ)] ![(43602111826377/100000000000000 : ℝ), (11262146317891/25000000000000 : ℝ), (11349302887059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635243/5000000 : ℝ)|^4483 ≤ (43602111826377/100000000000000 : ℝ)^3459
        have hw : |(2635243/5000000 : ℝ)|=(2635243/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404888971/10000000000 : ℝ)|^4483 ≤ (11262146317891/25000000000000 : ℝ)^3459
        have hw : |(5404888971/10000000000 : ℝ)|=(5404888971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1865656471/10000000000 : ℝ)|^4483 ≤ (11349302887059/100000000000000 : ℝ)^3459
        have hw : |(-1865656471/10000000000 : ℝ)|=(1865656471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_box_3 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4482658953/10000000000 : ℝ)*x 0 + (2091916671/5000000000 : ℝ)*x 1 + (2091917031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4482658953/10000000000 : ℝ)^4483 ≤ (35348953758969/100000000000000 : ℝ)^3459 := by
    have hnat : (4482658953 : ℕ)^4483*100000000000000^3459 ≤ 35348953758969^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482658953 10000000000 35348953758969 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2091916671/5000000000 : ℝ)^4483 ≤ (2020344969373/6250000000000 : ℝ)^3459 := by
    have hnat : (2091916671 : ℕ)^4483*6250000000000^3459 ≤ 2020344969373^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091916671 5000000000 2020344969373 6250000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2091917031/5000000000 : ℝ)^4483 ≤ (6465105343949/20000000000000 : ℝ)^3459 := by
    have hnat : (2091917031 : ℕ)^4483*20000000000000^3459 ≤ 6465105343949^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091917031 5000000000 6465105343949 20000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4482658953/10000000000 : ℝ), (2091916671/5000000000 : ℝ), (2091917031/5000000000 : ℝ)] ![(35348953758969/100000000000000 : ℝ), (2020344969373/6250000000000 : ℝ), (6465105343949/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4482658953/10000000000 : ℝ)|^4483 ≤ (35348953758969/100000000000000 : ℝ)^3459
        have hw : |(4482658953/10000000000 : ℝ)|=(4482658953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2091916671/5000000000 : ℝ)|^4483 ≤ (2020344969373/6250000000000 : ℝ)^3459
        have hw : |(2091916671/5000000000 : ℝ)|=(2091916671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2091917031/5000000000 : ℝ)|^4483 ≤ (6465105343949/20000000000000 : ℝ)^3459
        have hw : |(2091917031/5000000000 : ℝ)|=(2091917031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_box_4 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-264875097/1250000000 : ℝ)*x 0 + (5242956989/10000000000 : ℝ)*x 1 + (5242957127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264875097/1250000000 : ℝ)^4483 ≤ (6692824474263/50000000000000 : ℝ)^3459 := by
    have hnat : (264875097 : ℕ)^4483*50000000000000^3459 ≤ 6692824474263^3459*1250000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264875097 1250000000 6692824474263 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242956989/10000000000 : ℝ)^4483 ≤ (2165358738803/5000000000000 : ℝ)^3459 := by
    have hnat : (5242956989 : ℕ)^4483*5000000000000^3459 ≤ 2165358738803^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242956989 10000000000 2165358738803 5000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242957127/10000000000 : ℝ)^4483 ≤ (43307176253401/100000000000000 : ℝ)^3459 := by
    have hnat : (5242957127 : ℕ)^4483*100000000000000^3459 ≤ 43307176253401^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242957127 10000000000 43307176253401 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-264875097/1250000000 : ℝ), (5242956989/10000000000 : ℝ), (5242957127/10000000000 : ℝ)] ![(6692824474263/50000000000000 : ℝ), (2165358738803/5000000000000 : ℝ), (43307176253401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-264875097/1250000000 : ℝ)|^4483 ≤ (6692824474263/50000000000000 : ℝ)^3459
        have hw : |(-264875097/1250000000 : ℝ)|=(264875097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242956989/10000000000 : ℝ)|^4483 ≤ (2165358738803/5000000000000 : ℝ)^3459
        have hw : |(5242956989/10000000000 : ℝ)|=(5242956989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242957127/10000000000 : ℝ)|^4483 ≤ (43307176253401/100000000000000 : ℝ)^3459
        have hw : |(5242957127/10000000000 : ℝ)|=(5242957127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_box_5 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383393079/10000000000 : ℝ)*x 0 + (-966075763/5000000000 : ℝ)*x 1 + (5242957209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383393079/10000000000 : ℝ)^4483 ≤ (22408259493817/50000000000000 : ℝ)^3459 := by
    have hnat : (5383393079 : ℕ)^4483*50000000000000^3459 ≤ 22408259493817^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383393079 10000000000 22408259493817 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (966075763/5000000000 : ℝ)^4483 ≤ (1484537983689/12500000000000 : ℝ)^3459 := by
    have hnat : (966075763 : ℕ)^4483*12500000000000^3459 ≤ 1484537983689^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966075763 5000000000 1484537983689 12500000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242957209/10000000000 : ℝ)^4483 ≤ (21653588565621/50000000000000 : ℝ)^3459 := by
    have hnat : (5242957209 : ℕ)^4483*50000000000000^3459 ≤ 21653588565621^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242957209 10000000000 21653588565621 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383393079/10000000000 : ℝ), (-966075763/5000000000 : ℝ), (5242957209/10000000000 : ℝ)] ![(22408259493817/50000000000000 : ℝ), (1484537983689/12500000000000 : ℝ), (21653588565621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383393079/10000000000 : ℝ)|^4483 ≤ (22408259493817/50000000000000 : ℝ)^3459
        have hw : |(5383393079/10000000000 : ℝ)|=(5383393079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-966075763/5000000000 : ℝ)|^4483 ≤ (1484537983689/12500000000000 : ℝ)^3459
        have hw : |(-966075763/5000000000 : ℝ)|=(966075763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242957209/10000000000 : ℝ)|^4483 ≤ (21653588565621/50000000000000 : ℝ)^3459
        have hw : |(5242957209/10000000000 : ℝ)|=(5242957209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_box_6 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076678587/2000000000 : ℝ)*x 0 + (5242957569/10000000000 : ℝ)*x 1 + (-483037809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076678587/2000000000 : ℝ)^4483 ≤ (896330348679/2000000000000 : ℝ)^3459 := by
    have hnat : (1076678587 : ℕ)^4483*2000000000000^3459 ≤ 896330348679^3459*2000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076678587 2000000000 896330348679 2000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242957569/10000000000 : ℝ)^4483 ≤ (1732287239407/4000000000000 : ℝ)^3459 := by
    have hnat : (5242957569 : ℕ)^4483*4000000000000^3459 ≤ 1732287239407^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242957569 10000000000 1732287239407 4000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (483037809/2500000000 : ℝ)^4483 ≤ (11876301559277/100000000000000 : ℝ)^3459 := by
    have hnat : (483037809 : ℕ)^4483*100000000000000^3459 ≤ 11876301559277^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483037809 2500000000 11876301559277 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076678587/2000000000 : ℝ), (5242957569/10000000000 : ℝ), (-483037809/2500000000 : ℝ)] ![(896330348679/2000000000000 : ℝ), (1732287239407/4000000000000 : ℝ), (11876301559277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076678587/2000000000 : ℝ)|^4483 ≤ (896330348679/2000000000000 : ℝ)^3459
        have hw : |(1076678587/2000000000 : ℝ)|=(1076678587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242957569/10000000000 : ℝ)|^4483 ≤ (1732287239407/4000000000000 : ℝ)^3459
        have hw : |(5242957569/10000000000 : ℝ)|=(5242957569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-483037809/2500000000 : ℝ)|^4483 ≤ (11876301559277/100000000000000 : ℝ)^3459
        have hw : |(-483037809/2500000000 : ℝ)|=(483037809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_box_7 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4072423481/10000000000 : ℝ)*x 0 + (2194407237/5000000000 : ℝ)*x 1 + (4388814753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4072423481/10000000000 : ℝ)^4483 ≤ (31214333150883/100000000000000 : ℝ)^3459 := by
    have hnat : (4072423481 : ℕ)^4483*100000000000000^3459 ≤ 31214333150883^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4072423481 10000000000 31214333150883 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194407237/5000000000 : ℝ)^4483 ≤ (2149552000107/6250000000000 : ℝ)^3459 := by
    have hnat : (2194407237 : ℕ)^4483*6250000000000^3459 ≤ 2149552000107^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194407237 5000000000 2149552000107 6250000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4388814753/10000000000 : ℝ)^4483 ≤ (17196417417671/50000000000000 : ℝ)^3459 := by
    have hnat : (4388814753 : ℕ)^4483*50000000000000^3459 ≤ 17196417417671^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4388814753 10000000000 17196417417671 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4072423481/10000000000 : ℝ), (2194407237/5000000000 : ℝ), (4388814753/10000000000 : ℝ)] ![(31214333150883/100000000000000 : ℝ), (2149552000107/6250000000000 : ℝ), (17196417417671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4072423481/10000000000 : ℝ)|^4483 ≤ (31214333150883/100000000000000 : ℝ)^3459
        have hw : |(4072423481/10000000000 : ℝ)|=(4072423481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2194407237/5000000000 : ℝ)|^4483 ≤ (2149552000107/6250000000000 : ℝ)^3459
        have hw : |(2194407237/5000000000 : ℝ)|=(2194407237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4388814753/10000000000 : ℝ)|^4483 ≤ (17196417417671/50000000000000 : ℝ)^3459
        have hw : |(4388814753/10000000000 : ℝ)|=(4388814753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_box_8 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1013100917/5000000000 : ℝ)*x 0 + (2564862353/5000000000 : ℝ)*x 1 + (16954367/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1013100917/5000000000 : ℝ)^4483 ≤ (1263087754961/10000000000000 : ℝ)^3459 := by
    have hnat : (1013100917 : ℕ)^4483*10000000000000^3459 ≤ 1263087754961^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013100917 5000000000 1263087754961 10000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564862353/5000000000 : ℝ)^4483 ≤ (42098876087109/100000000000000 : ℝ)^3459 := by
    have hnat : (2564862353 : ℕ)^4483*100000000000000^3459 ≤ 42098876087109^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564862353 5000000000 42098876087109 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16954367/31250000 : ℝ)^4483 ≤ (22635123172887/50000000000000 : ℝ)^3459 := by
    have hnat : (16954367 : ℕ)^4483*50000000000000^3459 ≤ 22635123172887^3459*31250000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16954367 31250000 22635123172887 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1013100917/5000000000 : ℝ), (2564862353/5000000000 : ℝ), (16954367/31250000 : ℝ)] ![(1263087754961/10000000000000 : ℝ), (42098876087109/100000000000000 : ℝ), (22635123172887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1013100917/5000000000 : ℝ)|^4483 ≤ (1263087754961/10000000000000 : ℝ)^3459
        have hw : |(-1013100917/5000000000 : ℝ)|=(1013100917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564862353/5000000000 : ℝ)|^4483 ≤ (42098876087109/100000000000000 : ℝ)^3459
        have hw : |(2564862353/5000000000 : ℝ)|=(2564862353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16954367/31250000 : ℝ)|^4483 ≤ (22635123172887/50000000000000 : ℝ)^3459
        have hw : |(16954367/31250000 : ℝ)|=(16954367/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_box_9 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314044937/2500000000 : ℝ)*x 0 + (-11606151/62500000 : ℝ)*x 1 + (5425397019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314044937/2500000000 : ℝ)^4483 ≤ (43448782132643/100000000000000 : ℝ)^3459 := by
    have hnat : (1314044937 : ℕ)^4483*100000000000000^3459 ≤ 43448782132643^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314044937 2500000000 43448782132643 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11606151/62500000 : ℝ)^4483 ≤ (11280976055741/100000000000000 : ℝ)^3459 := by
    have hnat : (11606151 : ℕ)^4483*100000000000000^3459 ≤ 11280976055741^3459*62500000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11606151 62500000 11280976055741 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425397019/10000000000 : ℝ)^4483 ≤ (22635120896471/50000000000000 : ℝ)^3459 := by
    have hnat : (5425397019 : ℕ)^4483*50000000000000^3459 ≤ 22635120896471^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425397019 10000000000 22635120896471 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314044937/2500000000 : ℝ), (-11606151/62500000 : ℝ), (5425397019/10000000000 : ℝ)] ![(43448782132643/100000000000000 : ℝ), (11280976055741/100000000000000 : ℝ), (22635120896471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314044937/2500000000 : ℝ)|^4483 ≤ (43448782132643/100000000000000 : ℝ)^3459
        have hw : |(1314044937/2500000000 : ℝ)|=(1314044937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11606151/62500000 : ℝ)|^4483 ≤ (11280976055741/100000000000000 : ℝ)^3459
        have hw : |(-11606151/62500000 : ℝ)|=(11606151/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425397019/10000000000 : ℝ)|^4483 ≤ (22635120896471/50000000000000 : ℝ)^3459
        have hw : |(5425397019/10000000000 : ℝ)|=(5425397019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_box_10 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628089389/5000000000 : ℝ)*x 0 + (2712699113/5000000000 : ℝ)*x 1 + (-1856983823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628089389/5000000000 : ℝ)^4483 ≤ (43448771740687/100000000000000 : ℝ)^3459 := by
    have hnat : (2628089389 : ℕ)^4483*100000000000000^3459 ≤ 43448771740687^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628089389 5000000000 43448771740687 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712699113/5000000000 : ℝ)^4483 ≤ (9054050969167/20000000000000 : ℝ)^3459 := by
    have hnat : (2712699113 : ℕ)^4483*20000000000000^3459 ≤ 9054050969167^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712699113 5000000000 9054050969167 20000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1856983823/10000000000 : ℝ)^4483 ≤ (282024335061/2500000000000 : ℝ)^3459 := by
    have hnat : (1856983823 : ℕ)^4483*2500000000000^3459 ≤ 282024335061^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856983823 10000000000 282024335061 2500000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628089389/5000000000 : ℝ), (2712699113/5000000000 : ℝ), (-1856983823/10000000000 : ℝ)] ![(43448771740687/100000000000000 : ℝ), (9054050969167/20000000000000 : ℝ), (282024335061/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628089389/5000000000 : ℝ)|^4483 ≤ (43448771740687/100000000000000 : ℝ)^3459
        have hw : |(2628089389/5000000000 : ℝ)|=(2628089389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712699113/5000000000 : ℝ)|^4483 ≤ (9054050969167/20000000000000 : ℝ)^3459
        have hw : |(2712699113/5000000000 : ℝ)|=(2712699113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1856983823/10000000000 : ℝ)|^4483 ≤ (282024335061/2500000000000 : ℝ)^3459
        have hw : |(-1856983823/10000000000 : ℝ)|=(1856983823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_box_11 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1133365067/2500000000 : ℝ)*x 0 + (1039460487/2500000000 : ℝ)*x 1 + (166313653/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1133365067/2500000000 : ℝ)^4483 ≤ (896725539543/2500000000000 : ℝ)^3459 := by
    have hnat : (1133365067 : ℕ)^4483*2500000000000^3459 ≤ 896725539543^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133365067 2500000000 896725539543 2500000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039460487/2500000000 : ℝ)^4483 ≤ (32065492319579/100000000000000 : ℝ)^3459 := by
    have hnat : (1039460487 : ℕ)^4483*100000000000000^3459 ≤ 32065492319579^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039460487 2500000000 32065492319579 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166313653/400000000 : ℝ)^4483 ≤ (16032743046309/50000000000000 : ℝ)^3459 := by
    have hnat : (166313653 : ℕ)^4483*50000000000000^3459 ≤ 16032743046309^3459*400000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166313653 400000000 16032743046309 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1133365067/2500000000 : ℝ), (1039460487/2500000000 : ℝ), (166313653/400000000 : ℝ)] ![(896725539543/2500000000000 : ℝ), (32065492319579/100000000000000 : ℝ), (16032743046309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1133365067/2500000000 : ℝ)|^4483 ≤ (896725539543/2500000000000 : ℝ)^3459
        have hw : |(1133365067/2500000000 : ℝ)|=(1133365067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039460487/2500000000 : ℝ)|^4483 ≤ (32065492319579/100000000000000 : ℝ)^3459
        have hw : |(1039460487/2500000000 : ℝ)|=(1039460487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166313653/400000000 : ℝ)|^4483 ≤ (16032743046309/50000000000000 : ℝ)^3459
        have hw : |(166313653/400000000 : ℝ)|=(166313653/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_box_12 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-886112243/5000000000 : ℝ)*x 0 + (2757206999/5000000000 : ℝ)*x 1 + (5227948803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (886112243/5000000000 : ℝ)^4483 ≤ (5309097919171/50000000000000 : ℝ)^3459 := by
    have hnat : (886112243 : ℕ)^4483*50000000000000^3459 ≤ 5309097919171^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886112243 5000000000 5309097919171 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2757206999/5000000000 : ℝ)^4483 ≤ (9247045888643/20000000000000 : ℝ)^3459 := by
    have hnat : (2757206999 : ℕ)^4483*20000000000000^3459 ≤ 9247045888643^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757206999 5000000000 9247045888643 20000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227948803/10000000000 : ℝ)^4483 ≤ (8629314939077/20000000000000 : ℝ)^3459 := by
    have hnat : (5227948803 : ℕ)^4483*20000000000000^3459 ≤ 8629314939077^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227948803 10000000000 8629314939077 20000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-886112243/5000000000 : ℝ), (2757206999/5000000000 : ℝ), (5227948803/10000000000 : ℝ)] ![(5309097919171/50000000000000 : ℝ), (9247045888643/20000000000000 : ℝ), (8629314939077/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-886112243/5000000000 : ℝ)|^4483 ≤ (5309097919171/50000000000000 : ℝ)^3459
        have hw : |(-886112243/5000000000 : ℝ)|=(886112243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2757206999/5000000000 : ℝ)|^4483 ≤ (9247045888643/20000000000000 : ℝ)^3459
        have hw : |(2757206999/5000000000 : ℝ)|=(2757206999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227948803/10000000000 : ℝ)|^4483 ≤ (8629314939077/20000000000000 : ℝ)^3459
        have hw : |(5227948803/10000000000 : ℝ)|=(5227948803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_box_13 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393857191/10000000000 : ℝ)*x 0 + (-1938132989/10000000000 : ℝ)*x 1 + (522794839/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393857191/10000000000 : ℝ)^4483 ≤ (22464726851833/50000000000000 : ℝ)^3459 := by
    have hnat : (5393857191 : ℕ)^4483*50000000000000^3459 ≤ 22464726851833^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393857191 10000000000 22464726851833 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1938132989/10000000000 : ℝ)^4483 ≤ (11923975997023/100000000000000 : ℝ)^3459 := by
    have hnat : (1938132989 : ℕ)^4483*100000000000000^3459 ≤ 11923975997023^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938132989 10000000000 11923975997023 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522794839/1000000000 : ℝ)^4483 ≤ (43146570277817/100000000000000 : ℝ)^3459 := by
    have hnat : (522794839 : ℕ)^4483*100000000000000^3459 ≤ 43146570277817^3459*1000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522794839 1000000000 43146570277817 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393857191/10000000000 : ℝ), (-1938132989/10000000000 : ℝ), (522794839/1000000000 : ℝ)] ![(22464726851833/50000000000000 : ℝ), (11923975997023/100000000000000 : ℝ), (43146570277817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393857191/10000000000 : ℝ)|^4483 ≤ (22464726851833/50000000000000 : ℝ)^3459
        have hw : |(5393857191/10000000000 : ℝ)|=(5393857191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1938132989/10000000000 : ℝ)|^4483 ≤ (11923975997023/100000000000000 : ℝ)^3459
        have hw : |(-1938132989/10000000000 : ℝ)|=(1938132989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522794839/1000000000 : ℝ)|^4483 ≤ (43146570277817/100000000000000 : ℝ)^3459
        have hw : |(522794839/1000000000 : ℝ)|=(522794839/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_box_14 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696928493/5000000000 : ℝ)*x 0 + (5227948723/10000000000 : ℝ)*x 1 + (-1938132821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696928493/5000000000 : ℝ)^4483 ≤ (44929451490553/100000000000000 : ℝ)^3459 := by
    have hnat : (2696928493 : ℕ)^4483*100000000000000^3459 ≤ 44929451490553^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696928493 5000000000 44929451490553 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227948723/10000000000 : ℝ)^4483 ≤ (21573286919841/50000000000000 : ℝ)^3459 := by
    have hnat : (5227948723 : ℕ)^4483*50000000000000^3459 ≤ 21573286919841^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227948723 10000000000 21573286919841 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1938132821/10000000000 : ℝ)^4483 ≤ (5961987328727/50000000000000 : ℝ)^3459 := by
    have hnat : (1938132821 : ℕ)^4483*50000000000000^3459 ≤ 5961987328727^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938132821 10000000000 5961987328727 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696928493/5000000000 : ℝ), (5227948723/10000000000 : ℝ), (-1938132821/10000000000 : ℝ)] ![(44929451490553/100000000000000 : ℝ), (21573286919841/50000000000000 : ℝ), (5961987328727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696928493/5000000000 : ℝ)|^4483 ≤ (44929451490553/100000000000000 : ℝ)^3459
        have hw : |(2696928493/5000000000 : ℝ)|=(2696928493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227948723/10000000000 : ℝ)|^4483 ≤ (21573286919841/50000000000000 : ℝ)^3459
        have hw : |(5227948723/10000000000 : ℝ)|=(5227948723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1938132821/10000000000 : ℝ)|^4483 ≤ (5961987328727/50000000000000 : ℝ)^3459
        have hw : |(-1938132821/10000000000 : ℝ)|=(1938132821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_box_15 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (504192737/1250000000 : ℝ)*x 0 + (550973859/1250000000 : ℝ)*x 1 + (2203895027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (504192737/1250000000 : ℝ)^4483 ≤ (15414317438819/50000000000000 : ℝ)^3459 := by
    have hnat : (504192737 : ℕ)^4483*50000000000000^3459 ≤ 15414317438819^3459*1250000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504192737 1250000000 15414317438819 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550973859/1250000000 : ℝ)^4483 ≤ (34585686714033/100000000000000 : ℝ)^3459 := by
    have hnat : (550973859 : ℕ)^4483*100000000000000^3459 ≤ 34585686714033^3459*1250000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550973859 1250000000 34585686714033 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203895027/5000000000 : ℝ)^4483 ≤ (34585678395497/100000000000000 : ℝ)^3459 := by
    have hnat : (2203895027 : ℕ)^4483*100000000000000^3459 ≤ 34585678395497^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203895027 5000000000 34585678395497 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(504192737/1250000000 : ℝ), (550973859/1250000000 : ℝ), (2203895027/5000000000 : ℝ)] ![(15414317438819/50000000000000 : ℝ), (34585686714033/100000000000000 : ℝ), (34585678395497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(504192737/1250000000 : ℝ)|^4483 ≤ (15414317438819/50000000000000 : ℝ)^3459
        have hw : |(504192737/1250000000 : ℝ)|=(504192737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(550973859/1250000000 : ℝ)|^4483 ≤ (34585686714033/100000000000000 : ℝ)^3459
        have hw : |(550973859/1250000000 : ℝ)|=(550973859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2203895027/5000000000 : ℝ)|^4483 ≤ (34585678395497/100000000000000 : ℝ)^3459
        have hw : |(2203895027/5000000000 : ℝ)|=(2203895027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1493_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (271/2500 : ℝ)*pair X i i ≤ pair X i h) :
    -(15929/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58539/100000 : ℝ) ∧ (80113/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85879/100000 : ℝ) := by
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
  have lower0 : (271/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7739/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (271/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7739/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (271/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7739/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (271/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7739/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (271/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7739/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (271/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (271/2500 : ℝ) ^ (4481/1024 : ℝ) ≤ (5988399361981741/100000000000000000000 : ℝ) := by
    have hpowers : (271/2500 : ℝ)^4481 ≤ (5988399361981741/100000000000000000000 : ℝ)^1024 := by
      have hnat : (271 : ℕ)^4481*100000000000000000000^1024 ≤ 5988399361981741^1024*2500^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        271 2500 5988399361981741 100000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (271/2500 : ℝ)) (X := (5988399361981741/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7739/50000 : ℝ) ^ (4481/1024 : ℝ) ≤ (14229221680479983/50000000000000000000 : ℝ) := by
    have hpowers : (7739/50000 : ℝ)^4481 ≤ (14229221680479983/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7739 : ℕ)^4481*50000000000000000000^1024 ≤ 14229221680479983^1024*50000^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7739 50000 14229221680479983 50000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7739/50000 : ℝ)) (X := (14229221680479983/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005988399361981741/50000000000000000000 : ℝ) ≤ (10000273681663341/10000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (50005988399361981741/50000000000000000000 : ℝ)^1024 ≤ (10000273681663341/10000000000000000 : ℝ)^4481 := by
      have hnat : (50005988399361981741 : ℕ)^1024*10000000000000000^4481 ≤ 10000273681663341^4481*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005988399361981741 50000000000000000000 10000273681663341 10000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000273681663341/10000000000000000 : ℝ)) (X := (50005988399361981741/50000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034446842722941707/100000000000000000000 : ℝ) ≤ (2000157415223923/2000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (100034446842722941707/100000000000000000000 : ℝ)^1024 ≤ (2000157415223923/2000000000000000 : ℝ)^4481 := by
      have hnat : (100034446842722941707 : ℕ)^1024*2000000000000000^4481 ≤ 2000157415223923^4481*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034446842722941707 100000000000000000000 2000157415223923 2000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000157415223923/2000000000000000 : ℝ)) (X := (100034446842722941707/100000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014229221680479983/25000000000000000000 : ℝ) ≤ (10001300470575889/10000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (25014229221680479983/25000000000000000000 : ℝ)^1024 ≤ (10001300470575889/10000000000000000 : ℝ)^4481 := by
      have hnat : (25014229221680479983 : ℕ)^1024*10000000000000000^4481 ≤ 10001300470575889^4481*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014229221680479983 25000000000000000000 10001300470575889 10000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001300470575889/10000000000000000 : ℝ)) (X := (25014229221680479983/25000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5988399361981741/100000000000000000000 : ℝ) ≤ ((23185069471871277619/23190000000000000000 : ℝ)+2*(256697228137/231900000000000 : ℝ)*(271/2500 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (23185069471871277619/23190000000000000000 : ℝ)+2*(256697228137/231900000000000 : ℝ)*(271/2500 : ℝ)=(10000273681663341/10000000000000000 : ℝ) by norm_num, show 1+2*(5988399361981741/100000000000000000000 : ℝ)=(50005988399361981741/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14229221680479983/50000000000000000000 : ℝ)+(5988399361981741/100000000000000000000 : ℝ) ≤ ((23185069471871277619/23190000000000000000 : ℝ)+(256697228137/231900000000000 : ℝ)*((7739/50000 : ℝ)+(271/2500 : ℝ)))^(4481/1024 : ℝ) := by
    rw [show (23185069471871277619/23190000000000000000 : ℝ)+(256697228137/231900000000000 : ℝ)*((7739/50000 : ℝ)+(271/2500 : ℝ))=(2000157415223923/2000000000000000 : ℝ) by norm_num, show 1+(14229221680479983/50000000000000000000 : ℝ)+(5988399361981741/100000000000000000000 : ℝ)=(100034446842722941707/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14229221680479983/50000000000000000000 : ℝ) ≤ ((23185069471871277619/23190000000000000000 : ℝ)+2*(256697228137/231900000000000 : ℝ)*(7739/50000 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (23185069471871277619/23190000000000000000 : ℝ)+2*(256697228137/231900000000000 : ℝ)*(7739/50000 : ℝ)=(10001300470575889/10000000000000000 : ℝ) by norm_num, show 1+2*(14229221680479983/50000000000000000000 : ℝ)=(25014229221680479983/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23185069471871277619/23190000000000000000 : ℝ)*(X 1 0+X 2 0)+(256697228137/231900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (271/2500 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (23185069471871277619/23190000000000000000 : ℝ)) (alpha := (256697228137/231900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23185069471871277619/23190000000000000000 : ℝ)*(X 0 1+X 2 1)+(256697228137/231900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (271/2500 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (23185069471871277619/23190000000000000000 : ℝ)) (alpha := (256697228137/231900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23185069471871277619/23190000000000000000 : ℝ)*(X 0 2+X 1 2)+(256697228137/231900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (271/2500 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (23185069471871277619/23190000000000000000 : ℝ)) (alpha := (256697228137/231900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1679370541/10000000000 : ℝ)*X 0 0+(5404889733/10000000000 : ℝ)*X 0 1+(1080977583/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1317621397/2500000000 : ℝ)*X 1 0+(-466414379/2500000000 : ℝ)*X 1 1+(5404888617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635243/5000000 : ℝ)*X 2 0+(5404888971/10000000000 : ℝ)*X 2 1+(-1865656471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4482658953/10000000000 : ℝ)*X 0 0+(2091916671/5000000000 : ℝ)*X 0 1+(2091917031/5000000000 : ℝ)*X 0 2+(4482658953/10000000000 : ℝ)*X 1 0+(2091916671/5000000000 : ℝ)*X 1 1+(2091917031/5000000000 : ℝ)*X 1 2+(4482658953/10000000000 : ℝ)*X 2 0+(2091916671/5000000000 : ℝ)*X 2 1+(2091917031/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-264875097/1250000000 : ℝ)*X 0 0+(5242956989/10000000000 : ℝ)*X 0 1+(5242957127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5383393079/10000000000 : ℝ)*X 1 0+(-966075763/5000000000 : ℝ)*X 1 1+(5242957209/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1076678587/2000000000 : ℝ)*X 2 0+(5242957569/10000000000 : ℝ)*X 2 1+(-483037809/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4072423481/10000000000 : ℝ)*X 0 0+(2194407237/5000000000 : ℝ)*X 0 1+(4388814753/10000000000 : ℝ)*X 0 2+(4072423481/10000000000 : ℝ)*X 1 0+(2194407237/5000000000 : ℝ)*X 1 1+(4388814753/10000000000 : ℝ)*X 1 2+(4072423481/10000000000 : ℝ)*X 2 0+(2194407237/5000000000 : ℝ)*X 2 1+(4388814753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1013100917/5000000000 : ℝ)*X 0 0+(2564862353/5000000000 : ℝ)*X 0 1+(16954367/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1314044937/2500000000 : ℝ)*X 1 0+(-11606151/62500000 : ℝ)*X 1 1+(5425397019/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2628089389/5000000000 : ℝ)*X 2 0+(2712699113/5000000000 : ℝ)*X 2 1+(-1856983823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1133365067/2500000000 : ℝ)*X 0 0+(1039460487/2500000000 : ℝ)*X 0 1+(166313653/400000000 : ℝ)*X 0 2+(1133365067/2500000000 : ℝ)*X 1 0+(1039460487/2500000000 : ℝ)*X 1 1+(166313653/400000000 : ℝ)*X 1 2+(1133365067/2500000000 : ℝ)*X 2 0+(1039460487/2500000000 : ℝ)*X 2 1+(166313653/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-886112243/5000000000 : ℝ)*X 0 0+(2757206999/5000000000 : ℝ)*X 0 1+(5227948803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5393857191/10000000000 : ℝ)*X 1 0+(-1938132989/10000000000 : ℝ)*X 1 1+(522794839/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2696928493/5000000000 : ℝ)*X 2 0+(5227948723/10000000000 : ℝ)*X 2 1+(-1938132821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((504192737/1250000000 : ℝ)*X 0 0+(550973859/1250000000 : ℝ)*X 0 1+(2203895027/5000000000 : ℝ)*X 0 2+(504192737/1250000000 : ℝ)*X 1 0+(550973859/1250000000 : ℝ)*X 1 1+(2203895027/5000000000 : ℝ)*X 1 2+(504192737/1250000000 : ℝ)*X 2 0+(550973859/1250000000 : ℝ)*X 2 1+(2203895027/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15929/25000 : ℝ) ≤ (-246252854248106251596181428492759/386500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3662779/20000000000000 : ℝ)*(upper0) + (28266849/100000000000000 : ℝ)*(lower2) + (4879707/100000000000000 : ℝ)*(lower3) + (6194303/10000000000000 : ℝ)*(upper5) + (2195205372717939/100000000000000 : ℝ)*(major0) + (2195205372717939/100000000000000 : ℝ)*(major1) + (2195205372717939/100000000000000 : ℝ)*(major2) + (244738559/50000000000000 : ℝ)*(sp3) + (3055436302358177/100000000000000 : ℝ)*(sp4) + (152770817894727/5000000000000 : ℝ)*(sp5) + (1527673648699879/50000000000000 : ℝ)*(sp6) + (339052950544347/25000000000000 : ℝ)*(sp7) + (19944463637/100000000000000 : ℝ)*(sp13) + (89004958419/100000000000000 : ℝ)*(sp14) + (678106145827253/50000000000000 : ℝ)*(f.failure) + (3055436302358177/100000000000000 : ℝ)*(f.sum) + (14328340406569/3865000000000000000000000000 : ℝ)*base66 + (2376611775328064253/773000000000000000000000000000000 : ℝ)*base68 + (391930519497935747/773000000000000000000000000000000 : ℝ)*base69 + (5124863381352064253/773000000000000000000000000000000 : ℝ)*base72 + (8684545398303/1932500000000000000000000000 : ℝ)*base73 + (1164548122405064253/773000000000000000000000000000000 : ℝ)*base76 + (9246671402453064253/773000000000000000000000000000000 : ℝ)*base78 + (4409889016893935747/773000000000000000000000000000000 : ℝ)*base79 + (2166433437867/483125000000000000000000000 : ℝ)*base81 + (15076133/5000000000000000000000 : ℝ)*base89 + (15076133/5000000000000000000000 : ℝ)*base91 + (15076133/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58539/100000 : ℝ) ≤ (28282602785339477954759263306517/48312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (124162237/50000000000000 : ℝ)*(upper0) + (34738677/100000000000000 : ℝ)*(lower1) + (186305577/50000000000000 : ℝ)*(upper4) + (283771904928119/12500000000000 : ℝ)*(major0) + (283771904928119/12500000000000 : ℝ)*(major1) + (283771904928119/12500000000000 : ℝ)*(major2) + (389786243541939/12500000000000 : ℝ)*(sp0) + (3118298526759129/100000000000000 : ℝ)*(sp1) + (155913845193623/5000000000000 : ℝ)*(sp2) + (350629266917053/25000000000000 : ℝ)*(sp3) + (4565109883/50000000000000 : ℝ)*(sp5) + (15376553217/50000000000000 : ℝ)*(sp6) + (12099844639/100000000000000 : ℝ)*(sp7) + (8854321691/50000000000000 : ℝ)*(sp8) + (350632291878213/25000000000000 : ℝ)*(f.failure) + (623661531395779/20000000000000 : ℝ)*(f.sum) + (28290145400501/11595000000000000000000000000 : ℝ)*base66 + (3592019879121018661/289875000000000000000000000000000 : ℝ)*base67 + (4018265850212643661/289875000000000000000000000000000 : ℝ)*base69 + (558049167973893661/289875000000000000000000000000000 : ℝ)*base71 + (2824567483513/5797500000000000000000000000 : ℝ)*base74 + (2746570274398518661/289875000000000000000000000000000 : ℝ)*base75 + (2720843813941893661/289875000000000000000000000000000 : ℝ)*base77 + (3878809560353268661/289875000000000000000000000000000 : ℝ)*base79 + (28438398917359/11595000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (7568693/2500000000000000000000 : ℝ)*base89 + (7568693/2500000000000000000000 : ℝ)*base91 + (7568693/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (80113/100000 : ℝ) ≤ (154822243807693120962764277681/193250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (105632141/100000000000000 : ℝ)*(upper1) + (187833/312500000000 : ℝ)*(upper2) + (18870633/50000000000000 : ℝ)*(lower5) + (2466244452699/100000000000 : ℝ)*(major0) + (2466244452699/100000000000 : ℝ)*(major1) + (2466244452699/100000000000 : ℝ)*(major2) + (37457902499/20000000000000 : ℝ)*(sp2) + (10537248393/50000000000000 : ℝ)*(sp3) + (1220812399/100000000000000 : ℝ)*(sp4) + (338211993526279/10000000000000 : ℝ)*(sp8) + (845530472391173/25000000000000 : ℝ)*(sp9) + (3381934600052197/100000000000000 : ℝ)*(sp10) + (304728188049703/20000000000000 : ℝ)*(sp11) + (22921547/3125000000000 : ℝ)*(sp12) + (1523662014745301/100000000000000 : ℝ)*(f.failure) + (845530472391173/25000000000000 : ℝ)*(f.sum) + (4818049549/3092000000000000000000000 : ℝ)*base66 + (4885906270493773/773000000000000000000000000000 : ℝ)*base68 + (5334962622734773/773000000000000000000000000000 : ℝ)*base70 + (1972597062080773/773000000000000000000000000000 : ℝ)*base72 + (52917219003/96625000000000000000000000 : ℝ)*base73 + (3883592529266227/773000000000000000000000000000 : ℝ)*base75 + (2482767515530773/773000000000000000000000000000 : ℝ)*base78 + (1020382040445773/773000000000000000000000000000 : ℝ)*base80 + (1439503825837/773000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (80696261/10000000000000000000000 : ℝ)*base89 + (80696261/10000000000000000000000 : ℝ)*base91 + (80696261/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-85879/100000 : ℝ) ≤ (-165955971314674699734576980176851/193250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12980001/25000000000000 : ℝ)*(lower0) + (25660793/50000000000000 : ℝ)*(upper1) + (318863/1250000000000 : ℝ)*(lower2) + (46380747/100000000000000 : ℝ)*(upper3) + (327427/1250000000000 : ℝ)*(upper5) + (1252428295543871/50000000000000 : ℝ)*(major0) + (1252428295543871/50000000000000 : ℝ)*(major1) + (1252428295543871/50000000000000 : ℝ)*(major2) + (46382763489/50000000000000 : ℝ)*(sp5) + (2311774023/100000000000000 : ℝ)*(sp7) + (872705442970669/25000000000000 : ℝ)*(sp12) + (1745364503177849/50000000000000 : ℝ)*(sp13) + (872705442970669/25000000000000 : ℝ)*(sp14) + (309502907114353/20000000000000 : ℝ)*(sp15) + (386879211836447/25000000000000 : ℝ)*(f.failure) + (872705442970669/25000000000000 : ℝ)*(f.sum) + (11804941040711/11595000000000000000000000000 : ℝ)*base66 + (4910511870582623149/1159500000000000000000000000000000 : ℝ)*base67 + (5047722655323876851/1159500000000000000000000000000000 : ℝ)*base70 + (1099725598170876851/1159500000000000000000000000000000 : ℝ)*base72 + (38263161223307/5797500000000000000000000000 : ℝ)*base73 + (7441943819466876851/1159500000000000000000000000000000 : ℝ)*base76 + (2028328514652876851/1159500000000000000000000000000000 : ℝ)*base78 + (2647255876632623149/1159500000000000000000000000000000 : ℝ)*base79 + (100519232957981/11595000000000000000000000000 : ℝ)*base82 + (9139567/2500000000000000000000 : ℝ)*base89 + (9139567/2500000000000000000000 : ℝ)*base91 + (9139567/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1493_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (271/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15929/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58539/100000 : ℝ) else (80113/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85879/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1493_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1493_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10839/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15929/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58539/100000 : ℝ) else (80113/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85879/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1493_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1493_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1493_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10839/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15929/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58539/100000 : ℝ) else (80113/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85879/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1493_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

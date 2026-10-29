-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1344_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:05:25.34211+00:00
-- url     : https://prove2.me/submissions/f1fe0318-649d-4eff-97b9-b65cef6b203b

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
theorem support_rectangle_w1344_s6_0 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-31910021/156250000 : ℝ)*x 0 + (1082523143/2000000000 : ℝ)*x 1 + (209786379/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31910021/156250000 : ℝ)^269 ≤ (3109323171663/25000000000000 : ℝ)^205 := by
    have hnat : (31910021 : ℕ)^269*25000000000000^205 ≤ 3109323171663^205*156250000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31910021 156250000 3109323171663 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082523143/2000000000 : ℝ)^269 ≤ (44686693446241/100000000000000 : ℝ)^205 := by
    have hnat : (1082523143 : ℕ)^269*100000000000000^205 ≤ 44686693446241^205*2000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082523143 2000000000 44686693446241 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209786379/400000000 : ℝ)^269 ≤ (2679750865457/6250000000000 : ℝ)^205 := by
    have hnat : (209786379 : ℕ)^269*6250000000000^205 ≤ 2679750865457^205*400000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209786379 400000000 2679750865457 6250000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31910021/156250000 : ℝ), (1082523143/2000000000 : ℝ), (209786379/400000000 : ℝ)] ![(3109323171663/25000000000000 : ℝ), (44686693446241/100000000000000 : ℝ), (2679750865457/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31910021/156250000 : ℝ)|^269 ≤ (3109323171663/25000000000000 : ℝ)^205
        have hw : |(-31910021/156250000 : ℝ)|=(31910021/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082523143/2000000000 : ℝ)|^269 ≤ (44686693446241/100000000000000 : ℝ)^205
        have hw : |(1082523143/2000000000 : ℝ)|=(1082523143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209786379/400000000 : ℝ)|^269 ≤ (2679750865457/6250000000000 : ℝ)^205
        have hw : |(209786379/400000000 : ℝ)|=(209786379/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s6_1 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2674483337/5000000000 : ℝ)*x 0 + (-1063907421/5000000000 : ℝ)*x 1 + (1311164869/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674483337/5000000000 : ℝ)^269 ≤ (43998419678751/100000000000000 : ℝ)^205 := by
    have hnat : (2674483337 : ℕ)^269*100000000000000^205 ≤ 43998419678751^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674483337 5000000000 43998419678751 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1063907421/5000000000 : ℝ)^269 ≤ (6562783227697/50000000000000 : ℝ)^205 := by
    have hnat : (1063907421 : ℕ)^269*50000000000000^205 ≤ 6562783227697^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063907421 5000000000 6562783227697 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311164869/2500000000 : ℝ)^269 ≤ (42876013858039/100000000000000 : ℝ)^205 := by
    have hnat : (1311164869 : ℕ)^269*100000000000000^205 ≤ 42876013858039^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311164869 2500000000 42876013858039 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674483337/5000000000 : ℝ), (-1063907421/5000000000 : ℝ), (1311164869/2500000000 : ℝ)] ![(43998419678751/100000000000000 : ℝ), (6562783227697/50000000000000 : ℝ), (42876013858039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674483337/5000000000 : ℝ)|^269 ≤ (43998419678751/100000000000000 : ℝ)^205
        have hw : |(2674483337/5000000000 : ℝ)|=(2674483337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1063907421/5000000000 : ℝ)|^269 ≤ (6562783227697/50000000000000 : ℝ)^205
        have hw : |(-1063907421/5000000000 : ℝ)|=(1063907421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311164869/2500000000 : ℝ)|^269 ≤ (42876013858039/100000000000000 : ℝ)^205
        have hw : |(1311164869/2500000000 : ℝ)|=(1311164869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s6_2 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5348966671/10000000000 : ℝ)*x 0 + (5244659477/10000000000 : ℝ)*x 1 + (-2127814843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348966671/10000000000 : ℝ)^269 ≤ (4399841964637/10000000000000 : ℝ)^205 := by
    have hnat : (5348966671 : ℕ)^269*10000000000000^205 ≤ 4399841964637^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348966671 10000000000 4399841964637 10000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244659477/10000000000 : ℝ)^269 ≤ (42876013868767/100000000000000 : ℝ)^205 := by
    have hnat : (5244659477 : ℕ)^269*100000000000000^205 ≤ 42876013868767^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244659477 10000000000 42876013868767 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2127814843/10000000000 : ℝ)^269 ≤ (25635871999/195312500000 : ℝ)^205 := by
    have hnat : (2127814843 : ℕ)^269*195312500000^205 ≤ 25635871999^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127814843 10000000000 25635871999 195312500000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348966671/10000000000 : ℝ), (5244659477/10000000000 : ℝ), (-2127814843/10000000000 : ℝ)] ![(4399841964637/10000000000000 : ℝ), (42876013868767/100000000000000 : ℝ), (25635871999/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348966671/10000000000 : ℝ)|^269 ≤ (4399841964637/10000000000000 : ℝ)^205
        have hw : |(5348966671/10000000000 : ℝ)|=(5348966671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244659477/10000000000 : ℝ)|^269 ≤ (42876013868767/100000000000000 : ℝ)^205
        have hw : |(5244659477/10000000000 : ℝ)|=(5244659477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2127814843/10000000000 : ℝ)|^269 ≤ (25635871999/195312500000 : ℝ)^205
        have hw : |(-2127814843/10000000000 : ℝ)|=(2127814843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s6_3 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2163047631/5000000000 : ℝ)*x 0 + (2076704389/5000000000 : ℝ)*x 1 + (450547/1000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163047631/5000000000 : ℝ)^269 ≤ (832582077853/2500000000000 : ℝ)^205 := by
    have hnat : (2163047631 : ℕ)^269*2500000000000^205 ≤ 832582077853^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163047631 5000000000 832582077853 2500000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076704389/5000000000 : ℝ)^269 ≤ (7892461762927/25000000000000 : ℝ)^205 := by
    have hnat : (2076704389 : ℕ)^269*25000000000000^205 ≤ 7892461762927^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076704389 5000000000 7892461762927 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450547/1000000 : ℝ)^269 ≤ (35126869821607/100000000000000 : ℝ)^205 := by
    have hnat : (450547 : ℕ)^269*100000000000000^205 ≤ 35126869821607^205*1000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450547 1000000 35126869821607 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163047631/5000000000 : ℝ), (2076704389/5000000000 : ℝ), (450547/1000000 : ℝ)] ![(832582077853/2500000000000 : ℝ), (7892461762927/25000000000000 : ℝ), (35126869821607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163047631/5000000000 : ℝ)|^269 ≤ (832582077853/2500000000000 : ℝ)^205
        have hw : |(2163047631/5000000000 : ℝ)|=(2163047631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2076704389/5000000000 : ℝ)|^269 ≤ (7892461762927/25000000000000 : ℝ)^205
        have hw : |(2076704389/5000000000 : ℝ)|=(2076704389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450547/1000000 : ℝ)|^269 ≤ (35126869821607/100000000000000 : ℝ)^205
        have hw : |(450547/1000000 : ℝ)|=(450547/1000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s6_4 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2042253707/10000000000 : ℝ)*x 0 + (1049052141/2000000000 : ℝ)*x 1 + (5412011233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042253707/10000000000 : ℝ)^269 ≤ (48583560481/390625000000 : ℝ)^205 := by
    have hnat : (2042253707 : ℕ)^269*390625000000^205 ≤ 48583560481^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042253707 10000000000 48583560481 390625000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049052141/2000000000 : ℝ)^269 ≤ (21441231806517/50000000000000 : ℝ)^205 := by
    have hnat : (1049052141 : ℕ)^269*50000000000000^205 ≤ 21441231806517^205*2000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049052141 2000000000 21441231806517 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412011233/10000000000 : ℝ)^269 ≤ (22340072447371/50000000000000 : ℝ)^205 := by
    have hnat : (5412011233 : ℕ)^269*50000000000000^205 ≤ 22340072447371^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412011233 10000000000 22340072447371 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2042253707/10000000000 : ℝ), (1049052141/2000000000 : ℝ), (5412011233/10000000000 : ℝ)] ![(48583560481/390625000000 : ℝ), (21441231806517/50000000000000 : ℝ), (22340072447371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2042253707/10000000000 : ℝ)|^269 ≤ (48583560481/390625000000 : ℝ)^205
        have hw : |(-2042253707/10000000000 : ℝ)|=(2042253707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049052141/2000000000 : ℝ)|^269 ≤ (21441231806517/50000000000000 : ℝ)^205
        have hw : |(1049052141/2000000000 : ℝ)|=(1049052141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412011233/10000000000 : ℝ)|^269 ≤ (22340072447371/50000000000000 : ℝ)^205
        have hw : |(5412011233/10000000000 : ℝ)|=(5412011233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s6_5 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2652847687/5000000000 : ℝ)*x 0 + (-490115767/2500000000 : ℝ)*x 1 + (5412010819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652847687/5000000000 : ℝ)^269 ≤ (170046711811/390625000000 : ℝ)^205 := by
    have hnat : (2652847687 : ℕ)^269*390625000000^205 ≤ 170046711811^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652847687 5000000000 170046711811 390625000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (490115767/2500000000 : ℝ)^269 ≤ (5893950672571/50000000000000 : ℝ)^205 := by
    have hnat : (490115767 : ℕ)^269*50000000000000^205 ≤ 5893950672571^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490115767 2500000000 5893950672571 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412010819/10000000000 : ℝ)^269 ≤ (22340070204911/50000000000000 : ℝ)^205 := by
    have hnat : (5412010819 : ℕ)^269*50000000000000^205 ≤ 22340070204911^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412010819 10000000000 22340070204911 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652847687/5000000000 : ℝ), (-490115767/2500000000 : ℝ), (5412010819/10000000000 : ℝ)] ![(170046711811/390625000000 : ℝ), (5893950672571/50000000000000 : ℝ), (22340070204911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652847687/5000000000 : ℝ)|^269 ≤ (170046711811/390625000000 : ℝ)^205
        have hw : |(2652847687/5000000000 : ℝ)|=(2652847687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-490115767/2500000000 : ℝ)|^269 ≤ (5893950672571/50000000000000 : ℝ)^205
        have hw : |(-490115767/2500000000 : ℝ)|=(490115767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412010819/10000000000 : ℝ)|^269 ≤ (22340070204911/50000000000000 : ℝ)^205
        have hw : |(5412010819/10000000000 : ℝ)|=(5412010819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s6_6 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (331605963/625000000 : ℝ)*x 0 + (1353002673/2500000000 : ℝ)*x 1 + (-980231599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331605963/625000000 : ℝ)^269 ≤ (10882989647417/25000000000000 : ℝ)^205 := by
    have hnat : (331605963 : ℕ)^269*25000000000000^205 ≤ 10882989647417^205*625000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331605963 625000000 10882989647417 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353002673/2500000000 : ℝ)^269 ≤ (22340069517007/50000000000000 : ℝ)^205 := by
    have hnat : (1353002673 : ℕ)^269*50000000000000^205 ≤ 22340069517007^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353002673 2500000000 22340069517007 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (980231599/5000000000 : ℝ)^269 ≤ (294697559271/2500000000000 : ℝ)^205 := by
    have hnat : (980231599 : ℕ)^269*2500000000000^205 ≤ 294697559271^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980231599 5000000000 294697559271 2500000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331605963/625000000 : ℝ), (1353002673/2500000000 : ℝ), (-980231599/5000000000 : ℝ)] ![(10882989647417/25000000000000 : ℝ), (22340069517007/50000000000000 : ℝ), (294697559271/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331605963/625000000 : ℝ)|^269 ≤ (10882989647417/25000000000000 : ℝ)^205
        have hw : |(331605963/625000000 : ℝ)|=(331605963/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353002673/2500000000 : ℝ)|^269 ≤ (22340069517007/50000000000000 : ℝ)^205
        have hw : |(1353002673/2500000000 : ℝ)|=(1353002673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-980231599/5000000000 : ℝ)|^269 ≤ (294697559271/2500000000000 : ℝ)^205
        have hw : |(-980231599/5000000000 : ℝ)|=(980231599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s6_7 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4326120633/10000000000 : ℝ)*x 0 + (4504209307/10000000000 : ℝ)*x 1 + (4154676091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326120633/10000000000 : ℝ)^269 ≤ (3330353940159/10000000000000 : ℝ)^205 := by
    have hnat : (4326120633 : ℕ)^269*10000000000000^205 ≤ 3330353940159^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326120633 10000000000 3330353940159 10000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504209307/10000000000 : ℝ)^269 ≤ (35113972838277/100000000000000 : ℝ)^205 := by
    have hnat : (4504209307 : ℕ)^269*100000000000000^205 ≤ 35113972838277^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504209307 10000000000 35113972838277 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4154676091/10000000000 : ℝ)^269 ≤ (7895621935519/25000000000000 : ℝ)^205 := by
    have hnat : (4154676091 : ℕ)^269*25000000000000^205 ≤ 7895621935519^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154676091 10000000000 7895621935519 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326120633/10000000000 : ℝ), (4504209307/10000000000 : ℝ), (4154676091/10000000000 : ℝ)] ![(3330353940159/10000000000000 : ℝ), (35113972838277/100000000000000 : ℝ), (7895621935519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326120633/10000000000 : ℝ)|^269 ≤ (3330353940159/10000000000000 : ℝ)^205
        have hw : |(4326120633/10000000000 : ℝ)|=(4326120633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504209307/10000000000 : ℝ)|^269 ≤ (35113972838277/100000000000000 : ℝ)^205
        have hw : |(4504209307/10000000000 : ℝ)|=(4504209307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4154676091/10000000000 : ℝ)|^269 ≤ (7895621935519/25000000000000 : ℝ)^205
        have hw : |(4154676091/10000000000 : ℝ)|=(4154676091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1344_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11153/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14709/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3679/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5573/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3679/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5573/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3679/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5573/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3679/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5573/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3679/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5573/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3679/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5573/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5573/50000 : ℝ) ^ (4303/1024 : ℝ) ≤ (9904960716206147/100000000000000000000 : ℝ) := by
    have hpowers : (5573/50000 : ℝ)^4303 ≤ (9904960716206147/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5573 : ℕ)^4303*100000000000000000000^1024 ≤ 9904960716206147^1024*50000^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5573 50000 9904960716206147 100000000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5573/50000 : ℝ)) (X := (9904960716206147/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3679/25000 : ℝ) ^ (4303/1024 : ℝ) ≤ (7959194715237069/25000000000000000000 : ℝ) := by
    have hpowers : (3679/25000 : ℝ)^4303 ≤ (7959194715237069/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3679 : ℕ)^4303*25000000000000000000^1024 ≤ 7959194715237069^1024*25000^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3679 25000 7959194715237069 25000000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3679/25000 : ℝ)) (X := (7959194715237069/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009904960716206147/50000000000000000000 : ℝ) ≤ (5000235694034603/5000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (50009904960716206147/50000000000000000000 : ℝ)^1024 ≤ (5000235694034603/5000000000000000 : ℝ)^4303 := by
      have hnat : (50009904960716206147 : ℕ)^1024*5000000000000000^4303 ≤ 5000235694034603^4303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009904960716206147 50000000000000000000 5000235694034603 5000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000235694034603/5000000000000000 : ℝ)) (X := (50009904960716206147/50000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041741739577154423/100000000000000000000 : ℝ) ≤ (10000993184870877/10000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (100041741739577154423/100000000000000000000 : ℝ)^1024 ≤ (10000993184870877/10000000000000000 : ℝ)^4303 := by
      have hnat : (100041741739577154423 : ℕ)^1024*10000000000000000^4303 ≤ 10000993184870877^4303*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041741739577154423 100000000000000000000 10000993184870877 10000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000993184870877/10000000000000000 : ℝ)) (X := (100041741739577154423/100000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507959194715237069/12500000000000000000 : ℝ) ≤ (2500378745418137/2500000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (12507959194715237069/12500000000000000000 : ℝ)^1024 ≤ (2500378745418137/2500000000000000 : ℝ)^4303 := by
      have hnat : (12507959194715237069 : ℕ)^1024*2500000000000000^4303 ≤ 2500378745418137^4303*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507959194715237069 12500000000000000000 2500378745418137 2500000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500378745418137/2500000000000000 : ℝ)) (X := (12507959194715237069/12500000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9904960716206147/100000000000000000000 : ℝ) ≤ ((557657046267253367/557812500000000000 : ℝ)+2*(521796801671/357000000000000 : ℝ)*(5573/50000 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (557657046267253367/557812500000000000 : ℝ)+2*(521796801671/357000000000000 : ℝ)*(5573/50000 : ℝ)=(5000235694034603/5000000000000000 : ℝ) by norm_num, show 1+2*(9904960716206147/100000000000000000000 : ℝ)=(50009904960716206147/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7959194715237069/25000000000000000000 : ℝ)+(9904960716206147/100000000000000000000 : ℝ) ≤ ((557657046267253367/557812500000000000 : ℝ)+(521796801671/357000000000000 : ℝ)*((3679/25000 : ℝ)+(5573/50000 : ℝ)))^(4303/1024 : ℝ) := by
    rw [show (557657046267253367/557812500000000000 : ℝ)+(521796801671/357000000000000 : ℝ)*((3679/25000 : ℝ)+(5573/50000 : ℝ))=(10000993184870877/10000000000000000 : ℝ) by norm_num, show 1+(7959194715237069/25000000000000000000 : ℝ)+(9904960716206147/100000000000000000000 : ℝ)=(100041741739577154423/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7959194715237069/25000000000000000000 : ℝ) ≤ ((557657046267253367/557812500000000000 : ℝ)+2*(521796801671/357000000000000 : ℝ)*(3679/25000 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (557657046267253367/557812500000000000 : ℝ)+2*(521796801671/357000000000000 : ℝ)*(3679/25000 : ℝ)=(2500378745418137/2500000000000000 : ℝ) by norm_num, show 1+2*(7959194715237069/25000000000000000000 : ℝ)=(12507959194715237069/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (557657046267253367/557812500000000000 : ℝ)*(X 1 0+X 2 0)+(521796801671/357000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (5573/50000 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (557657046267253367/557812500000000000 : ℝ)) (alpha := (521796801671/357000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (557657046267253367/557812500000000000 : ℝ)*(X 0 1+X 2 1)+(521796801671/357000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (5573/50000 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (557657046267253367/557812500000000000 : ℝ)) (alpha := (521796801671/357000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (557657046267253367/557812500000000000 : ℝ)*(X 0 2+X 1 2)+(521796801671/357000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (5573/50000 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (557657046267253367/557812500000000000 : ℝ)) (alpha := (521796801671/357000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-31910021/156250000 : ℝ)*X 0 0+(1082523143/2000000000 : ℝ)*X 0 1+(209786379/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674483337/5000000000 : ℝ)*X 1 0+(-1063907421/5000000000 : ℝ)*X 1 1+(1311164869/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348966671/10000000000 : ℝ)*X 2 0+(5244659477/10000000000 : ℝ)*X 2 1+(-2127814843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2163047631/5000000000 : ℝ)*X 0 0+(2076704389/5000000000 : ℝ)*X 0 1+(450547/1000000 : ℝ)*X 0 2+(2163047631/5000000000 : ℝ)*X 1 0+(2076704389/5000000000 : ℝ)*X 1 1+(450547/1000000 : ℝ)*X 1 2+(2163047631/5000000000 : ℝ)*X 2 0+(2076704389/5000000000 : ℝ)*X 2 1+(450547/1000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2042253707/10000000000 : ℝ)*X 0 0+(1049052141/2000000000 : ℝ)*X 0 1+(5412011233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652847687/5000000000 : ℝ)*X 1 0+(-490115767/2500000000 : ℝ)*X 1 1+(5412010819/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331605963/625000000 : ℝ)*X 2 0+(1353002673/2500000000 : ℝ)*X 2 1+(-980231599/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4326120633/10000000000 : ℝ)*X 0 0+(4504209307/10000000000 : ℝ)*X 0 1+(4154676091/10000000000 : ℝ)*X 0 2+(4326120633/10000000000 : ℝ)*X 1 0+(4504209307/10000000000 : ℝ)*X 1 1+(4154676091/10000000000 : ℝ)*X 1 2+(4326120633/10000000000 : ℝ)*X 2 0+(4504209307/10000000000 : ℝ)*X 2 1+(4154676091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (82388152373094158161496307/9296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1671570393/100000000000000 : ℝ)*(base19) + (38743397/2500000000000 : ℝ)*(base23) + (15845669/25000000000000 : ℝ)*(lower2) + (228696281/100000000000000 : ℝ)*(upper3) + (34662241/25000000000000 : ℝ)*(upper5) + (549653104841019/12500000000000 : ℝ)*(major0) + (549653104841019/12500000000000 : ℝ)*(major1) + (549653104841019/12500000000000 : ℝ)*(major2) + (1190793476417089/20000000000000 : ℝ)*(sp0) + (5953999578564507/100000000000000 : ℝ)*(sp1) + (297699985019951/5000000000000 : ℝ)*(sp2) + (1420215317581189/50000000000000 : ℝ)*(sp3) + (16934024727/50000000000000 : ℝ)*(sp4) + (17496761721/100000000000000 : ℝ)*(sp7) + (28404481319241/1000000000000 : ℝ)*(f.failure) + (59540012501349/1000000000000 : ℝ)*(f.sum) + (653896763393/2975000000000000000000000000 : ℝ)*base66 + (23613803110077107/4648437500000000000000000000000 : ℝ)*base67 + (50799882604295857/4648437500000000000000000000000 : ℝ)*base69 + (23880634330548911/9296875000000000000000000000000 : ℝ)*base72 + (1613037257243/2975000000000000000000000000 : ℝ)*base74 + (18964862019138589/9296875000000000000000000000000 : ℝ)*base75 + (62777185861794839/9296875000000000000000000000000 : ℝ)*base77 + (86443319024451089/9296875000000000000000000000000 : ℝ)*base79 + (15312808106107/2975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (718353/100000000000000000000 : ℝ)*base89 + (718353/100000000000000000000 : ℝ)*base91 + (718353/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (110380801128143424176731341/18593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1100689371/50000000000000 : ℝ)*(base19) + (601044363/25000000000000 : ℝ)*(base23) + (112058707/100000000000000 : ℝ)*(upper2) + (7904463/10000000000000 : ℝ)*(upper3) + (260087149/100000000000000 : ℝ)*(upper5) + (4428970846964337/100000000000000 : ℝ)*(major0) + (4428970846964337/100000000000000 : ℝ)*(major1) + (4428970846964337/100000000000000 : ℝ)*(major2) + (40792640061/100000000000000 : ℝ)*(sp1) + (17524959159/50000000000000 : ℝ)*(sp2) + (5996986591534013/100000000000000 : ℝ)*(sp4) + (5996943597515211/100000000000000 : ℝ)*(sp5) + (5996949137438243/100000000000000 : ℝ)*(sp6) + (178809681532069/6250000000000 : ℝ)*(sp7) + (178809681532069/6250000000000 : ℝ)*(f.failure) + (5996986591534013/100000000000000 : ℝ)*(f.sum) + (9402406421759/5950000000000000000000000000 : ℝ)*base65 + (72991190910434911/37187500000000000000000000000000 : ℝ)*base67 + (339910784589565089/37187500000000000000000000000000 : ℝ)*base70 + (113913844799877589/37187500000000000000000000000000 : ℝ)*base72 + (43439336338609/5950000000000000000000000000 : ℝ)*base73 + (688445712747065089/37187500000000000000000000000000 : ℝ)*base76 + (759466773795502589/37187500000000000000000000000000 : ℝ)*base78 + (266174973640502589/37187500000000000000000000000000 : ℝ)*base80 + (23442724743509/5950000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2818877/625000000000000000000 : ℝ)*base89 + (2818877/625000000000000000000 : ℝ)*base91 + (2818877/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1344_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1344_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1344_s7_0 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1021123573/5000000000 : ℝ)*x 0 + (2706278943/5000000000 : ℝ)*x 1 + (2622356777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1021123573/5000000000 : ℝ)^269 ≤ (12437339052171/100000000000000 : ℝ)^205 := by
    have hnat : (1021123573 : ℕ)^269*100000000000000^205 ≤ 12437339052171^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021123573 5000000000 12437339052171 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706278943/5000000000 : ℝ)^269 ≤ (8937213391173/20000000000000 : ℝ)^205 := by
    have hnat : (2706278943 : ℕ)^269*20000000000000^205 ≤ 8937213391173^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706278943 5000000000 8937213391173 20000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622356777/5000000000 : ℝ)^269 ≤ (21438296988357/50000000000000 : ℝ)^205 := by
    have hnat : (2622356777 : ℕ)^269*50000000000000^205 ≤ 21438296988357^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622356777 5000000000 21438296988357 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1021123573/5000000000 : ℝ), (2706278943/5000000000 : ℝ), (2622356777/5000000000 : ℝ)] ![(12437339052171/100000000000000 : ℝ), (8937213391173/20000000000000 : ℝ), (21438296988357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1021123573/5000000000 : ℝ)|^269 ≤ (12437339052171/100000000000000 : ℝ)^205
        have hw : |(-1021123573/5000000000 : ℝ)|=(1021123573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706278943/5000000000 : ℝ)|^269 ≤ (8937213391173/20000000000000 : ℝ)^205
        have hw : |(2706278943/5000000000 : ℝ)|=(2706278943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622356777/5000000000 : ℝ)|^269 ≤ (21438296988357/50000000000000 : ℝ)^205
        have hw : |(2622356777/5000000000 : ℝ)|=(2622356777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s7_1 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5348952997/10000000000 : ℝ)*x 0 + (-2127761839/10000000000 : ℝ)*x 1 + (524471323/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348952997/10000000000 : ℝ)^269 ≤ (21999136027493/50000000000000 : ℝ)^205 := by
    have hnat : (5348952997 : ℕ)^269*50000000000000^205 ≤ 21999136027493^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348952997 10000000000 21999136027493 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2127761839/10000000000 : ℝ)^269 ≤ (1640642178947/12500000000000 : ℝ)^205 := by
    have hnat : (2127761839 : ℕ)^269*12500000000000^205 ≤ 1640642178947^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127761839 10000000000 1640642178947 12500000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524471323/1000000000 : ℝ)^269 ≤ (42876590501017/100000000000000 : ℝ)^205 := by
    have hnat : (524471323 : ℕ)^269*100000000000000^205 ≤ 42876590501017^205*1000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524471323 1000000000 42876590501017 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348952997/10000000000 : ℝ), (-2127761839/10000000000 : ℝ), (524471323/1000000000 : ℝ)] ![(21999136027493/50000000000000 : ℝ), (1640642178947/12500000000000 : ℝ), (42876590501017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348952997/10000000000 : ℝ)|^269 ≤ (21999136027493/50000000000000 : ℝ)^205
        have hw : |(5348952997/10000000000 : ℝ)|=(5348952997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2127761839/10000000000 : ℝ)|^269 ≤ (1640642178947/12500000000000 : ℝ)^205
        have hw : |(-2127761839/10000000000 : ℝ)|=(2127761839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524471323/1000000000 : ℝ)|^269 ≤ (42876590501017/100000000000000 : ℝ)^205
        have hw : |(524471323/1000000000 : ℝ)|=(524471323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s7_2 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (213958079/400000000 : ℝ)*x 0 + (131117847/250000000 : ℝ)*x 1 + (-106388117/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213958079/400000000 : ℝ)^269 ≤ (21999130511977/50000000000000 : ℝ)^205 := by
    have hnat : (213958079 : ℕ)^269*50000000000000^205 ≤ 21999130511977^205*400000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213958079 400000000 21999130511977 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131117847/250000000 : ℝ)^269 ≤ (21438298736933/50000000000000 : ℝ)^205 := by
    have hnat : (131117847 : ℕ)^269*50000000000000^205 ≤ 21438298736933^205*250000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131117847 250000000 21438298736933 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106388117/500000000 : ℝ)^269 ≤ (656257074341/5000000000000 : ℝ)^205 := by
    have hnat : (106388117 : ℕ)^269*5000000000000^205 ≤ 656257074341^205*500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106388117 500000000 656257074341 5000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213958079/400000000 : ℝ), (131117847/250000000 : ℝ), (-106388117/500000000 : ℝ)] ![(21999130511977/50000000000000 : ℝ), (21438298736933/50000000000000 : ℝ), (656257074341/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213958079/400000000 : ℝ)|^269 ≤ (21999130511977/50000000000000 : ℝ)^205
        have hw : |(213958079/400000000 : ℝ)|=(213958079/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131117847/250000000 : ℝ)|^269 ≤ (21438298736933/50000000000000 : ℝ)^205
        have hw : |(131117847/250000000 : ℝ)|=(131117847/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106388117/500000000 : ℝ)|^269 ≤ (656257074341/5000000000000 : ℝ)^205
        have hw : |(-106388117/500000000 : ℝ)|=(106388117/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s7_3 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2163049517/5000000000 : ℝ)*x 0 + (207676253/500000000 : ℝ)*x 1 + (4505352909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163049517/5000000000 : ℝ)^269 ≤ (8325830304323/25000000000000 : ℝ)^205 := by
    have hnat : (2163049517 : ℕ)^269*25000000000000^205 ≤ 8325830304323^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163049517 5000000000 8325830304323 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207676253/500000000 : ℝ)^269 ≤ (631420136901/2000000000000 : ℝ)^205 := by
    have hnat : (207676253 : ℕ)^269*2000000000000^205 ≤ 631420136901^205*500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207676253 500000000 631420136901 2000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505352909/10000000000 : ℝ)^269 ≤ (17562835962243/50000000000000 : ℝ)^205 := by
    have hnat : (4505352909 : ℕ)^269*50000000000000^205 ≤ 17562835962243^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505352909 10000000000 17562835962243 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163049517/5000000000 : ℝ), (207676253/500000000 : ℝ), (4505352909/10000000000 : ℝ)] ![(8325830304323/25000000000000 : ℝ), (631420136901/2000000000000 : ℝ), (17562835962243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163049517/5000000000 : ℝ)|^269 ≤ (8325830304323/25000000000000 : ℝ)^205
        have hw : |(2163049517/5000000000 : ℝ)|=(2163049517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207676253/500000000 : ℝ)|^269 ≤ (631420136901/2000000000000 : ℝ)^205
        have hw : |(207676253/500000000 : ℝ)|=(207676253/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505352909/10000000000 : ℝ)|^269 ≤ (17562835962243/50000000000000 : ℝ)^205
        have hw : |(4505352909/10000000000 : ℝ)|=(4505352909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s7_4 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2042259259/10000000000 : ℝ)*x 0 + (2622657059/5000000000 : ℝ)*x 1 + (2705977121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042259259/10000000000 : ℝ)^269 ≤ (6218717925457/50000000000000 : ℝ)^205 := by
    have hnat : (2042259259 : ℕ)^269*50000000000000^205 ≤ 6218717925457^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042259259 10000000000 6218717925457 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622657059/5000000000 : ℝ)^269 ≤ (42883036618453/100000000000000 : ℝ)^205 := by
    have hnat : (2622657059 : ℕ)^269*100000000000000^205 ≤ 42883036618453^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622657059 5000000000 42883036618453 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705977121/5000000000 : ℝ)^269 ≤ (44679527504351/100000000000000 : ℝ)^205 := by
    have hnat : (2705977121 : ℕ)^269*100000000000000^205 ≤ 44679527504351^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705977121 5000000000 44679527504351 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2042259259/10000000000 : ℝ), (2622657059/5000000000 : ℝ), (2705977121/5000000000 : ℝ)] ![(6218717925457/50000000000000 : ℝ), (42883036618453/100000000000000 : ℝ), (44679527504351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2042259259/10000000000 : ℝ)|^269 ≤ (6218717925457/50000000000000 : ℝ)^205
        have hw : |(-2042259259/10000000000 : ℝ)|=(2042259259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622657059/5000000000 : ℝ)|^269 ≤ (42883036618453/100000000000000 : ℝ)^205
        have hw : |(2622657059/5000000000 : ℝ)|=(2622657059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705977121/5000000000 : ℝ)|^269 ≤ (44679527504351/100000000000000 : ℝ)^205
        have hw : |(2705977121/5000000000 : ℝ)|=(2705977121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s7_5 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (132642731/250000000 : ℝ)*x 0 + (-980260657/5000000000 : ℝ)*x 1 + (5411954617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132642731/250000000 : ℝ)^269 ≤ (1360378359639/3125000000000 : ℝ)^205 := by
    have hnat : (132642731 : ℕ)^269*3125000000000^205 ≤ 1360378359639^205*250000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132642731 250000000 1360378359639 3125000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (980260657/5000000000 : ℝ)^269 ≤ (2947090226853/25000000000000 : ℝ)^205 := by
    have hnat : (980260657 : ℕ)^269*25000000000000^205 ≤ 2947090226853^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980260657 5000000000 2947090226853 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411954617/10000000000 : ℝ)^269 ≤ (11169882891691/25000000000000 : ℝ)^205 := by
    have hnat : (5411954617 : ℕ)^269*25000000000000^205 ≤ 11169882891691^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411954617 10000000000 11169882891691 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132642731/250000000 : ℝ), (-980260657/5000000000 : ℝ), (5411954617/10000000000 : ℝ)] ![(1360378359639/3125000000000 : ℝ), (2947090226853/25000000000000 : ℝ), (11169882891691/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132642731/250000000 : ℝ)|^269 ≤ (1360378359639/3125000000000 : ℝ)^205
        have hw : |(132642731/250000000 : ℝ)|=(132642731/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-980260657/5000000000 : ℝ)|^269 ≤ (2947090226853/25000000000000 : ℝ)^205
        have hw : |(-980260657/5000000000 : ℝ)|=(980260657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411954617/10000000000 : ℝ)|^269 ≤ (11169882891691/25000000000000 : ℝ)^205
        have hw : |(5411954617/10000000000 : ℝ)|=(5411954617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s7_6 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305708871/10000000000 : ℝ)*x 0 + (5411954543/10000000000 : ℝ)*x 1 + (-1960521919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305708871/10000000000 : ℝ)^269 ≤ (435321035357/1000000000000 : ℝ)^205 := by
    have hnat : (5305708871 : ℕ)^269*1000000000000^205 ≤ 435321035357^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305708871 10000000000 435321035357 1000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411954543/10000000000 : ℝ)^269 ≤ (8935906153023/20000000000000 : ℝ)^205 := by
    have hnat : (5411954543 : ℕ)^269*20000000000000^205 ≤ 8935906153023^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411954543 10000000000 8935906153023 20000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1960521919/10000000000 : ℝ)^269 ≤ (5894182840449/50000000000000 : ℝ)^205 := by
    have hnat : (1960521919 : ℕ)^269*50000000000000^205 ≤ 5894182840449^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960521919 10000000000 5894182840449 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305708871/10000000000 : ℝ), (5411954543/10000000000 : ℝ), (-1960521919/10000000000 : ℝ)] ![(435321035357/1000000000000 : ℝ), (8935906153023/20000000000000 : ℝ), (5894182840449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305708871/10000000000 : ℝ)|^269 ≤ (435321035357/1000000000000 : ℝ)^205
        have hw : |(5305708871/10000000000 : ℝ)|=(5305708871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411954543/10000000000 : ℝ)|^269 ≤ (8935906153023/20000000000000 : ℝ)^205
        have hw : |(5411954543/10000000000 : ℝ)|=(5411954543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1960521919/10000000000 : ℝ)|^269 ≤ (5894182840449/50000000000000 : ℝ)^205
        have hw : |(-1960521919/10000000000 : ℝ)|=(1960521919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s7_7 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4326124663/10000000000 : ℝ)*x 0 + (4504092857/10000000000 : ℝ)*x 1 + (4154791433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326124663/10000000000 : ℝ)^269 ≤ (6660716022209/20000000000000 : ℝ)^205 := by
    have hnat : (4326124663 : ℕ)^269*20000000000000^205 ≤ 6660716022209^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326124663 10000000000 6660716022209 20000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504092857/10000000000 : ℝ)^269 ≤ (702255632059/2000000000000 : ℝ)^205 := by
    have hnat : (4504092857 : ℕ)^269*2000000000000^205 ≤ 702255632059^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504092857 10000000000 702255632059 2000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4154791433/10000000000 : ℝ)^269 ≤ (31583638269419/100000000000000 : ℝ)^205 := by
    have hnat : (4154791433 : ℕ)^269*100000000000000^205 ≤ 31583638269419^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154791433 10000000000 31583638269419 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326124663/10000000000 : ℝ), (4504092857/10000000000 : ℝ), (4154791433/10000000000 : ℝ)] ![(6660716022209/20000000000000 : ℝ), (702255632059/2000000000000 : ℝ), (31583638269419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326124663/10000000000 : ℝ)|^269 ≤ (6660716022209/20000000000000 : ℝ)^205
        have hw : |(4326124663/10000000000 : ℝ)|=(4326124663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504092857/10000000000 : ℝ)|^269 ≤ (702255632059/2000000000000 : ℝ)^205
        have hw : |(4504092857/10000000000 : ℝ)|=(4504092857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4154791433/10000000000 : ℝ)|^269 ≤ (31583638269419/100000000000000 : ℝ)^205
        have hw : |(4154791433/10000000000 : ℝ)|=(4154791433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1344_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5577/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3677/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14709/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11153/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14709/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11153/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14709/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11153/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14709/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11153/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14709/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11153/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14709/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11153/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11153/100000 : ℝ) ^ (4303/1024 : ℝ) ≤ (9931126865890347/100000000000000000000 : ℝ) := by
    have hpowers : (11153/100000 : ℝ)^4303 ≤ (9931126865890347/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11153 : ℕ)^4303*100000000000000000000^1024 ≤ 9931126865890347^1024*100000^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11153 100000 9931126865890347 100000000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11153/100000 : ℝ)) (X := (9931126865890347/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14709/100000 : ℝ) ^ (4303/1024 : ℝ) ≤ (15886595222421173/50000000000000000000 : ℝ) := by
    have hpowers : (14709/100000 : ℝ)^4303 ≤ (15886595222421173/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14709 : ℕ)^4303*50000000000000000000^1024 ≤ 15886595222421173^1024*100000^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14709 100000 15886595222421173 50000000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14709/100000 : ℝ)) (X := (15886595222421173/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009931126865890347/50000000000000000000 : ℝ) ≤ (5000236316625537/5000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (50009931126865890347/50000000000000000000 : ℝ)^1024 ≤ (5000236316625537/5000000000000000 : ℝ)^4303 := by
      have hnat : (50009931126865890347 : ℕ)^1024*5000000000000000^4303 ≤ 5000236316625537^4303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009931126865890347 50000000000000000000 5000236316625537 5000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000236316625537/5000000000000000 : ℝ)) (X := (50009931126865890347/50000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041704317310732693/100000000000000000000 : ℝ) ≤ (10000992294603117/10000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (100041704317310732693/100000000000000000000 : ℝ)^1024 ≤ (10000992294603117/10000000000000000 : ℝ)^4303 := by
      have hnat : (100041704317310732693 : ℕ)^1024*10000000000000000^4303 ≤ 10000992294603117^4303*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041704317310732693 100000000000000000000 10000992294603117 10000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000992294603117/10000000000000000 : ℝ)) (X := (100041704317310732693/100000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015886595222421173/25000000000000000000 : ℝ) ≤ (250037798898879/250000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (25015886595222421173/25000000000000000000 : ℝ)^1024 ≤ (250037798898879/250000000000000 : ℝ)^4303 := by
      have hnat : (25015886595222421173 : ℕ)^1024*250000000000000^4303 ≤ 250037798898879^4303*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015886595222421173 25000000000000000000 250037798898879 250000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250037798898879/250000000000000 : ℝ)) (X := (25015886595222421173/25000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9931126865890347/100000000000000000000 : ℝ) ≤ ((17775044558861073993/17780000000000000000 : ℝ)+2*(519661352043/355600000000000 : ℝ)*(11153/100000 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (17775044558861073993/17780000000000000000 : ℝ)+2*(519661352043/355600000000000 : ℝ)*(11153/100000 : ℝ)=(5000236316625537/5000000000000000 : ℝ) by norm_num, show 1+2*(9931126865890347/100000000000000000000 : ℝ)=(50009931126865890347/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15886595222421173/50000000000000000000 : ℝ)+(9931126865890347/100000000000000000000 : ℝ) ≤ ((17775044558861073993/17780000000000000000 : ℝ)+(519661352043/355600000000000 : ℝ)*((14709/100000 : ℝ)+(11153/100000 : ℝ)))^(4303/1024 : ℝ) := by
    rw [show (17775044558861073993/17780000000000000000 : ℝ)+(519661352043/355600000000000 : ℝ)*((14709/100000 : ℝ)+(11153/100000 : ℝ))=(10000992294603117/10000000000000000 : ℝ) by norm_num, show 1+(15886595222421173/50000000000000000000 : ℝ)+(9931126865890347/100000000000000000000 : ℝ)=(100041704317310732693/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15886595222421173/50000000000000000000 : ℝ) ≤ ((17775044558861073993/17780000000000000000 : ℝ)+2*(519661352043/355600000000000 : ℝ)*(14709/100000 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (17775044558861073993/17780000000000000000 : ℝ)+2*(519661352043/355600000000000 : ℝ)*(14709/100000 : ℝ)=(250037798898879/250000000000000 : ℝ) by norm_num, show 1+2*(15886595222421173/50000000000000000000 : ℝ)=(25015886595222421173/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17775044558861073993/17780000000000000000 : ℝ)*(X 1 0+X 2 0)+(519661352043/355600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (11153/100000 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (17775044558861073993/17780000000000000000 : ℝ)) (alpha := (519661352043/355600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17775044558861073993/17780000000000000000 : ℝ)*(X 0 1+X 2 1)+(519661352043/355600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (11153/100000 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (17775044558861073993/17780000000000000000 : ℝ)) (alpha := (519661352043/355600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17775044558861073993/17780000000000000000 : ℝ)*(X 0 2+X 1 2)+(519661352043/355600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (11153/100000 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (17775044558861073993/17780000000000000000 : ℝ)) (alpha := (519661352043/355600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1021123573/5000000000 : ℝ)*X 0 0+(2706278943/5000000000 : ℝ)*X 0 1+(2622356777/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348952997/10000000000 : ℝ)*X 1 0+(-2127761839/10000000000 : ℝ)*X 1 1+(524471323/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213958079/400000000 : ℝ)*X 2 0+(131117847/250000000 : ℝ)*X 2 1+(-106388117/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2163049517/5000000000 : ℝ)*X 0 0+(207676253/500000000 : ℝ)*X 0 1+(4505352909/10000000000 : ℝ)*X 0 2+(2163049517/5000000000 : ℝ)*X 1 0+(207676253/500000000 : ℝ)*X 1 1+(4505352909/10000000000 : ℝ)*X 1 2+(2163049517/5000000000 : ℝ)*X 2 0+(207676253/500000000 : ℝ)*X 2 1+(4505352909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2042259259/10000000000 : ℝ)*X 0 0+(2622657059/5000000000 : ℝ)*X 0 1+(2705977121/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132642731/250000000 : ℝ)*X 1 0+(-980260657/5000000000 : ℝ)*X 1 1+(5411954617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305708871/10000000000 : ℝ)*X 2 0+(5411954543/10000000000 : ℝ)*X 2 1+(-1960521919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4326124663/10000000000 : ℝ)*X 0 0+(4504092857/10000000000 : ℝ)*X 0 1+(4154791433/10000000000 : ℝ)*X 0 2+(4326124663/10000000000 : ℝ)*X 1 0+(4504092857/10000000000 : ℝ)*X 1 1+(4154791433/10000000000 : ℝ)*X 1 2+(4326124663/10000000000 : ℝ)*X 2 0+(4504092857/10000000000 : ℝ)*X 2 1+(4154791433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (126982628974937946410418711/15875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2951999681/100000000000000 : ℝ)*(base19) + (197803937/10000000000000 : ℝ)*(base23) + (119949547/100000000000000 : ℝ)*(upper2) + (51541713/12500000000000 : ℝ)*(upper3) + (550024475319921/12500000000000 : ℝ)*(major0) + (550024475319921/12500000000000 : ℝ)*(major1) + (550024475319921/12500000000000 : ℝ)*(major2) + (595797633264339/10000000000000 : ℝ)*(sp0) + (1489505279858581/25000000000000 : ℝ)*(sp1) + (5958014691872167/100000000000000 : ℝ)*(sp2) + (56846653158269/2000000000000 : ℝ)*(sp3) + (9547758123/20000000000000 : ℝ)*(sp4) + (1850380617/25000000000000 : ℝ)*(sp6) + (17304570539/50000000000000 : ℝ)*(sp7) + (2842367267054527/100000000000000 : ℝ)*(f.failure) + (1489506017858501/25000000000000 : ℝ)*(f.sum) + (1731574348557/635000000000000000000000000 : ℝ)*base66 + (372691062101847921/31750000000000000000000000000000 : ℝ)*base68 + (435560658168347921/31750000000000000000000000000000 : ℝ)*base70 + (385275812332347921/31750000000000000000000000000000 : ℝ)*base72 + (93752822223/158750000000000000000000000 : ℝ)*base74 + (505993576420847921/31750000000000000000000000000000 : ℝ)*base76 + (677094012826097921/31750000000000000000000000000000 : ℝ)*base78 + (194385410776347921/31750000000000000000000000000000 : ℝ)*base80 + (927778783531/317500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4100809/10000000000000000000000 : ℝ)*base90 + (4100809/10000000000000000000000 : ℝ)*base92 + (4100809/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43647747854332382602784187/3968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1054730077/50000000000000 : ℝ)*(base19) + (1501979007/100000000000000 : ℝ)*(base23) + (261504849/50000000000000 : ℝ)*(lower1) + (32584701/100000000000000 : ℝ)*(upper2) + (153701299/100000000000000 : ℝ)*(upper3) + (25891451/6250000000000 : ℝ)*(upper5) + (276992630802271/6250000000000 : ℝ)*(major0) + (276992630802271/6250000000000 : ℝ)*(major1) + (276992630802271/6250000000000 : ℝ)*(major2) + (15431398881/50000000000000 : ℝ)*(sp1) + (6000928355074631/100000000000000 : ℝ)*(sp4) + (1200179076563343/20000000000000 : ℝ)*(sp5) + (750115856636953/12500000000000 : ℝ)*(sp6) + (357854433000347/12500000000000 : ℝ)*(sp7) + (357854433000347/12500000000000 : ℝ)*(f.failure) + (6000928355074631/100000000000000 : ℝ)*(f.sum) + (10036050873643/4445000000000000000000000000 : ℝ)*base66 + (600867740560161897/111125000000000000000000000000000 : ℝ)*base68 + (3393210208632661897/111125000000000000000000000000000 : ℝ)*base70 + (95525948731161897/111125000000000000000000000000000 : ℝ)*base72 + (171983490099/138906250000000000000000000 : ℝ)*base74 + (1050448479239786897/111125000000000000000000000000000 : ℝ)*base76 + (1119136238469911897/111125000000000000000000000000000 : ℝ)*base78 + (844615214004088103/111125000000000000000000000000000 : ℝ)*base79 + (1269537882493/1111250000000000000000000000 : ℝ)*base81 + (7179251/1250000000000000000000 : ℝ)*base89 + (7179251/1250000000000000000000 : ℝ)*base91 + (7179251/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1344_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11153/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1344_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1344_s8_0 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-408449537/2000000000 : ℝ)*x 0 + (5412550077/10000000000 : ℝ)*x 1 + (5244721039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (408449537/2000000000 : ℝ)^269 ≤ (3109335839871/25000000000000 : ℝ)^205 := by
    have hnat : (408449537 : ℕ)^269*25000000000000^205 ≤ 3109335839871^205*2000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408449537 2000000000 3109335839871 25000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412550077/10000000000 : ℝ)^269 ≤ (44685982357237/100000000000000 : ℝ)^205 := by
    have hnat : (5412550077 : ℕ)^269*100000000000000^205 ≤ 44685982357237^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412550077 10000000000 44685982357237 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244721039/10000000000 : ℝ)^269 ≤ (21438337135887/50000000000000 : ℝ)^205 := by
    have hnat : (5244721039 : ℕ)^269*50000000000000^205 ≤ 21438337135887^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244721039 10000000000 21438337135887 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-408449537/2000000000 : ℝ), (5412550077/10000000000 : ℝ), (5244721039/10000000000 : ℝ)] ![(3109335839871/25000000000000 : ℝ), (44685982357237/100000000000000 : ℝ), (21438337135887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-408449537/2000000000 : ℝ)|^269 ≤ (3109335839871/25000000000000 : ℝ)^205
        have hw : |(-408449537/2000000000 : ℝ)|=(408449537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412550077/10000000000 : ℝ)|^269 ≤ (44685982357237/100000000000000 : ℝ)^205
        have hw : |(5412550077/10000000000 : ℝ)|=(5412550077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244721039/10000000000 : ℝ)|^269 ≤ (21438337135887/50000000000000 : ℝ)^205
        have hw : |(5244721039/10000000000 : ℝ)|=(5244721039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s8_1 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5348950591/10000000000 : ℝ)*x 0 + (-531938687/2500000000 : ℝ)*x 1 + (2622360501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348950591/10000000000 : ℝ)^269 ≤ (43998246085649/100000000000000 : ℝ)^205 := by
    have hnat : (5348950591 : ℕ)^269*100000000000000^205 ≤ 43998246085649^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348950591 10000000000 43998246085649 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531938687/2500000000 : ℝ)^269 ≤ (13125080034929/100000000000000 : ℝ)^205 := by
    have hnat : (531938687 : ℕ)^269*100000000000000^205 ≤ 13125080034929^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531938687 2500000000 13125080034929 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622360501/5000000000 : ℝ)^269 ≤ (21438336937429/50000000000000 : ℝ)^205 := by
    have hnat : (2622360501 : ℕ)^269*50000000000000^205 ≤ 21438336937429^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622360501 5000000000 21438336937429 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348950591/10000000000 : ℝ), (-531938687/2500000000 : ℝ), (2622360501/5000000000 : ℝ)] ![(43998246085649/100000000000000 : ℝ), (13125080034929/100000000000000 : ℝ), (21438336937429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348950591/10000000000 : ℝ)|^269 ≤ (43998246085649/100000000000000 : ℝ)^205
        have hw : |(5348950591/10000000000 : ℝ)|=(5348950591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-531938687/2500000000 : ℝ)|^269 ≤ (13125080034929/100000000000000 : ℝ)^205
        have hw : |(-531938687/2500000000 : ℝ)|=(531938687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622360501/5000000000 : ℝ)|^269 ≤ (21438336937429/50000000000000 : ℝ)^205
        have hw : |(2622360501/5000000000 : ℝ)|=(2622360501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s8_2 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5348949907/10000000000 : ℝ)*x 0 + (5244721717/10000000000 : ℝ)*x 1 + (-2127754711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348949907/10000000000 : ℝ)^269 ≤ (21999119351423/50000000000000 : ℝ)^205 := by
    have hnat : (5348949907 : ℕ)^269*50000000000000^205 ≤ 21999119351423^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348949907 10000000000 21999119351423 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244721717/10000000000 : ℝ)^269 ≤ (8575336308999/20000000000000 : ℝ)^205 := by
    have hnat : (5244721717 : ℕ)^269*20000000000000^205 ≤ 8575336308999^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244721717 10000000000 8575336308999 20000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2127754711/10000000000 : ℝ)^269 ≤ (164063496693/1250000000000 : ℝ)^205 := by
    have hnat : (2127754711 : ℕ)^269*1250000000000^205 ≤ 164063496693^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127754711 10000000000 164063496693 1250000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348949907/10000000000 : ℝ), (5244721717/10000000000 : ℝ), (-2127754711/10000000000 : ℝ)] ![(21999119351423/50000000000000 : ℝ), (8575336308999/20000000000000 : ℝ), (164063496693/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348949907/10000000000 : ℝ)|^269 ≤ (21999119351423/50000000000000 : ℝ)^205
        have hw : |(5348949907/10000000000 : ℝ)|=(5348949907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244721717/10000000000 : ℝ)|^269 ≤ (8575336308999/20000000000000 : ℝ)^205
        have hw : |(5244721717/10000000000 : ℝ)|=(5244721717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2127754711/10000000000 : ℝ)|^269 ≤ (164063496693/1250000000000 : ℝ)^205
        have hw : |(-2127754711/10000000000 : ℝ)|=(2127754711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s8_3 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (432609937/1000000000 : ℝ)*x 0 + (2076771037/5000000000 : ℝ)*x 1 + (4505335989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432609937/1000000000 : ℝ)^269 ≤ (1332132984457/4000000000000 : ℝ)^205 := by
    have hnat : (432609937 : ℕ)^269*4000000000000^205 ≤ 1332132984457^205*1000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432609937 1000000000 1332132984457 4000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076771037/5000000000 : ℝ)^269 ≤ (31571176543049/100000000000000 : ℝ)^205 := by
    have hnat : (2076771037 : ℕ)^269*100000000000000^205 ≤ 31571176543049^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076771037 5000000000 31571176543049 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505335989/10000000000 : ℝ)^269 ≤ (3512549882557/10000000000000 : ℝ)^205 := by
    have hnat : (4505335989 : ℕ)^269*10000000000000^205 ≤ 3512549882557^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505335989 10000000000 3512549882557 10000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(432609937/1000000000 : ℝ), (2076771037/5000000000 : ℝ), (4505335989/10000000000 : ℝ)] ![(1332132984457/4000000000000 : ℝ), (31571176543049/100000000000000 : ℝ), (3512549882557/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(432609937/1000000000 : ℝ)|^269 ≤ (1332132984457/4000000000000 : ℝ)^205
        have hw : |(432609937/1000000000 : ℝ)|=(432609937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2076771037/5000000000 : ℝ)|^269 ≤ (31571176543049/100000000000000 : ℝ)^205
        have hw : |(2076771037/5000000000 : ℝ)|=(2076771037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505335989/10000000000 : ℝ)|^269 ≤ (3512549882557/10000000000000 : ℝ)^205
        have hw : |(4505335989/10000000000 : ℝ)|=(4505335989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s8_4 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1021129917/5000000000 : ℝ)*x 0 + (2622660937/5000000000 : ℝ)*x 1 + (2705973069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1021129917/5000000000 : ℝ)^269 ≤ (12437440445921/100000000000000 : ℝ)^205 := by
    have hnat : (1021129917 : ℕ)^269*100000000000000^205 ≤ 12437440445921^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021129917 5000000000 12437440445921 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622660937/5000000000 : ℝ)^269 ≤ (4288311982363/10000000000000 : ℝ)^205 := by
    have hnat : (2622660937 : ℕ)^269*10000000000000^205 ≤ 4288311982363^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622660937 5000000000 4288311982363 10000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705973069/5000000000 : ℝ)^269 ≤ (5584929964113/12500000000000 : ℝ)^205 := by
    have hnat : (2705973069 : ℕ)^269*12500000000000^205 ≤ 5584929964113^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705973069 5000000000 5584929964113 12500000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1021129917/5000000000 : ℝ), (2622660937/5000000000 : ℝ), (2705973069/5000000000 : ℝ)] ![(12437440445921/100000000000000 : ℝ), (4288311982363/10000000000000 : ℝ), (5584929964113/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1021129917/5000000000 : ℝ)|^269 ≤ (12437440445921/100000000000000 : ℝ)^205
        have hw : |(-1021129917/5000000000 : ℝ)|=(1021129917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622660937/5000000000 : ℝ)|^269 ≤ (4288311982363/10000000000000 : ℝ)^205
        have hw : |(2622660937/5000000000 : ℝ)|=(2622660937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705973069/5000000000 : ℝ)|^269 ≤ (5584929964113/12500000000000 : ℝ)^205
        have hw : |(2705973069/5000000000 : ℝ)|=(2705973069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s8_5 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (82901739/156250000 : ℝ)*x 0 + (-1960530117/10000000000 : ℝ)*x 1 + (2705973081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82901739/156250000 : ℝ)^269 ≤ (4353212964387/10000000000000 : ℝ)^205 := by
    have hnat : (82901739 : ℕ)^269*10000000000000^205 ≤ 4353212964387^205*156250000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82901739 156250000 4353212964387 10000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1960530117/10000000000 : ℝ)^269 ≤ (5894215181827/50000000000000 : ℝ)^205 := by
    have hnat : (1960530117 : ℕ)^269*50000000000000^205 ≤ 5894215181827^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960530117 10000000000 5894215181827 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705973081/5000000000 : ℝ)^269 ≤ (22339719986449/50000000000000 : ℝ)^205 := by
    have hnat : (2705973081 : ℕ)^269*50000000000000^205 ≤ 22339719986449^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705973081 5000000000 22339719986449 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82901739/156250000 : ℝ), (-1960530117/10000000000 : ℝ), (2705973081/5000000000 : ℝ)] ![(4353212964387/10000000000000 : ℝ), (5894215181827/50000000000000 : ℝ), (22339719986449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82901739/156250000 : ℝ)|^269 ≤ (4353212964387/10000000000000 : ℝ)^205
        have hw : |(82901739/156250000 : ℝ)|=(82901739/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1960530117/10000000000 : ℝ)|^269 ≤ (5894215181827/50000000000000 : ℝ)^205
        have hw : |(-1960530117/10000000000 : ℝ)|=(1960530117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705973081/5000000000 : ℝ)|^269 ≤ (22339719986449/50000000000000 : ℝ)^205
        have hw : |(2705973081/5000000000 : ℝ)|=(2705973081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s8_6 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305711359/10000000000 : ℝ)*x 0 + (2705973081/5000000000 : ℝ)*x 1 + (-122533127/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305711359/10000000000 : ℝ)^269 ≤ (1360379072567/3125000000000 : ℝ)^205 := by
    have hnat : (5305711359 : ℕ)^269*3125000000000^205 ≤ 1360379072567^205*10000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305711359 10000000000 1360379072567 3125000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705973081/5000000000 : ℝ)^269 ≤ (22339719986449/50000000000000 : ℝ)^205 := by
    have hnat : (2705973081 : ℕ)^269*50000000000000^205 ≤ 22339719986449^205*5000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705973081 5000000000 22339719986449 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122533127/625000000 : ℝ)^269 ≤ (5894214846499/50000000000000 : ℝ)^205 := by
    have hnat : (122533127 : ℕ)^269*50000000000000^205 ≤ 5894214846499^205*625000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122533127 625000000 5894214846499 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305711359/10000000000 : ℝ), (2705973081/5000000000 : ℝ), (-122533127/625000000 : ℝ)] ![(1360379072567/3125000000000 : ℝ), (22339719986449/50000000000000 : ℝ), (5894214846499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305711359/10000000000 : ℝ)|^269 ≤ (1360379072567/3125000000000 : ℝ)^205
        have hw : |(5305711359/10000000000 : ℝ)|=(5305711359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705973081/5000000000 : ℝ)|^269 ≤ (22339719986449/50000000000000 : ℝ)^205
        have hw : |(2705973081/5000000000 : ℝ)|=(2705973081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-122533127/625000000 : ℝ)|^269 ≤ (5894214846499/50000000000000 : ℝ)^205
        have hw : |(-122533127/625000000 : ℝ)|=(122533127/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1344_s8_7 (p : ℝ) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1081531313/2500000000 : ℝ)*x 0 + (450407673/1000000000 : ℝ)*x 1 + (33238459/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081531313/2500000000 : ℝ)^269 ≤ (3330358606089/10000000000000 : ℝ)^205 := by
    have hnat : (1081531313 : ℕ)^269*10000000000000^205 ≤ 3330358606089^205*2500000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081531313 2500000000 3330358606089 10000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450407673/1000000000 : ℝ)^269 ≤ (35112616631169/100000000000000 : ℝ)^205 := by
    have hnat : (450407673 : ℕ)^269*100000000000000^205 ≤ 35112616631169^205*1000000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450407673 1000000000 35112616631169 100000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33238459/80000000 : ℝ)^269 ≤ (15791898645197/50000000000000 : ℝ)^205 := by
    have hnat : (33238459 : ℕ)^269*50000000000000^205 ≤ 15791898645197^205*80000000^269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33238459 80000000 15791898645197 50000000000000 269 205 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (269/64 : ℝ)) 269 205 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081531313/2500000000 : ℝ), (450407673/1000000000 : ℝ), (33238459/80000000 : ℝ)] ![(3330358606089/10000000000000 : ℝ), (35112616631169/100000000000000 : ℝ), (15791898645197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081531313/2500000000 : ℝ)|^269 ≤ (3330358606089/10000000000000 : ℝ)^205
        have hw : |(1081531313/2500000000 : ℝ)|=(1081531313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(450407673/1000000000 : ℝ)|^269 ≤ (35112616631169/100000000000000 : ℝ)^205
        have hw : |(450407673/1000000000 : ℝ)|=(450407673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33238459/80000000 : ℝ)|^269 ≤ (15791898645197/50000000000000 : ℝ)^205
        have hw : |(33238459/80000000 : ℝ)|=(33238459/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1344_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2231/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14707/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3677/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5577/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3677/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5577/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3677/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5577/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3677/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5577/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3677/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5577/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3677/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5577/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5577/50000 : ℝ) ^ (4303/1024 : ℝ) ≤ (9934869182800907/100000000000000000000 : ℝ) := by
    have hpowers : (5577/50000 : ℝ)^4303 ≤ (9934869182800907/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5577 : ℕ)^4303*100000000000000000000^1024 ≤ 9934869182800907^1024*50000^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5577 50000 9934869182800907 100000000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5577/50000 : ℝ)) (X := (9934869182800907/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3677/25000 : ℝ) ^ (4303/1024 : ℝ) ≤ (31764114292137779/100000000000000000000 : ℝ) := by
    have hpowers : (3677/25000 : ℝ)^4303 ≤ (31764114292137779/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3677 : ℕ)^4303*100000000000000000000^1024 ≤ 31764114292137779^1024*25000^4303 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3677 25000 31764114292137779 100000000000000000000 4303 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3677/25000 : ℝ)) (X := (31764114292137779/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009934869182800907/50000000000000000000 : ℝ) ≤ (10000472811338571/10000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (50009934869182800907/50000000000000000000 : ℝ)^1024 ≤ (10000472811338571/10000000000000000 : ℝ)^4303 := by
      have hnat : (50009934869182800907 : ℕ)^1024*10000000000000000^4303 ≤ 10000472811338571^4303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009934869182800907 50000000000000000000 10000472811338571 10000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000472811338571/10000000000000000 : ℝ)) (X := (50009934869182800907/50000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020849491737469343/50000000000000000000 : ℝ) ≤ (10000992167712277/10000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (50020849491737469343/50000000000000000000 : ℝ)^1024 ≤ (10000992167712277/10000000000000000 : ℝ)^4303 := by
      have hnat : (50020849491737469343 : ℕ)^1024*10000000000000000^4303 ≤ 10000992167712277^4303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020849491737469343 50000000000000000000 10000992167712277 10000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000992167712277/10000000000000000 : ℝ)) (X := (50020849491737469343/50000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031764114292137779/50000000000000000000 : ℝ) ≤ (10001511524085983/10000000000000000 : ℝ) ^ (4303/1024 : ℝ) := by
    have hpowers : (50031764114292137779/50000000000000000000 : ℝ)^1024 ≤ (10001511524085983/10000000000000000 : ℝ)^4303 := by
      have hnat : (50031764114292137779 : ℕ)^1024*10000000000000000^4303 ≤ 10001511524085983^4303*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031764114292137779 50000000000000000000 10001511524085983 10000000000000000 1024 4303 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001511524085983/10000000000000000 : ℝ)) (X := (50031764114292137779/50000000000000000000 : ℝ)) (by norm_num) 4303 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9934869182800907/100000000000000000000 : ℝ) ≤ ((17765047284756323943/17770000000000000000 : ℝ)+2*(259678186853/177700000000000 : ℝ)*(5577/50000 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (17765047284756323943/17770000000000000000 : ℝ)+2*(259678186853/177700000000000 : ℝ)*(5577/50000 : ℝ)=(10000472811338571/10000000000000000 : ℝ) by norm_num, show 1+2*(9934869182800907/100000000000000000000 : ℝ)=(50009934869182800907/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31764114292137779/100000000000000000000 : ℝ)+(9934869182800907/100000000000000000000 : ℝ) ≤ ((17765047284756323943/17770000000000000000 : ℝ)+(259678186853/177700000000000 : ℝ)*((3677/25000 : ℝ)+(5577/50000 : ℝ)))^(4303/1024 : ℝ) := by
    rw [show (17765047284756323943/17770000000000000000 : ℝ)+(259678186853/177700000000000 : ℝ)*((3677/25000 : ℝ)+(5577/50000 : ℝ))=(10000992167712277/10000000000000000 : ℝ) by norm_num, show 1+(31764114292137779/100000000000000000000 : ℝ)+(9934869182800907/100000000000000000000 : ℝ)=(50020849491737469343/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31764114292137779/100000000000000000000 : ℝ) ≤ ((17765047284756323943/17770000000000000000 : ℝ)+2*(259678186853/177700000000000 : ℝ)*(3677/25000 : ℝ))^(4303/1024 : ℝ) := by
    rw [show (17765047284756323943/17770000000000000000 : ℝ)+2*(259678186853/177700000000000 : ℝ)*(3677/25000 : ℝ)=(10001511524085983/10000000000000000 : ℝ) by norm_num, show 1+2*(31764114292137779/100000000000000000000 : ℝ)=(50031764114292137779/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17765047284756323943/17770000000000000000 : ℝ)*(X 1 0+X 2 0)+(259678186853/177700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (5577/50000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (17765047284756323943/17770000000000000000 : ℝ)) (alpha := (259678186853/177700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17765047284756323943/17770000000000000000 : ℝ)*(X 0 1+X 2 1)+(259678186853/177700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (5577/50000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (17765047284756323943/17770000000000000000 : ℝ)) (alpha := (259678186853/177700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17765047284756323943/17770000000000000000 : ℝ)*(X 0 2+X 1 2)+(259678186853/177700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4303/1024 : ℝ)) (lo := (5577/50000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (17765047284756323943/17770000000000000000 : ℝ)) (alpha := (259678186853/177700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-408449537/2000000000 : ℝ)*X 0 0+(5412550077/10000000000 : ℝ)*X 0 1+(5244721039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348950591/10000000000 : ℝ)*X 1 0+(-531938687/2500000000 : ℝ)*X 1 1+(2622360501/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348949907/10000000000 : ℝ)*X 2 0+(5244721717/10000000000 : ℝ)*X 2 1+(-2127754711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((432609937/1000000000 : ℝ)*X 0 0+(2076771037/5000000000 : ℝ)*X 0 1+(4505335989/10000000000 : ℝ)*X 0 2+(432609937/1000000000 : ℝ)*X 1 0+(2076771037/5000000000 : ℝ)*X 1 1+(4505335989/10000000000 : ℝ)*X 1 2+(432609937/1000000000 : ℝ)*X 2 0+(2076771037/5000000000 : ℝ)*X 2 1+(4505335989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1021129917/5000000000 : ℝ)*X 0 0+(2622660937/5000000000 : ℝ)*X 0 1+(2705973069/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((82901739/156250000 : ℝ)*X 1 0+(-1960530117/10000000000 : ℝ)*X 1 1+(2705973081/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305711359/10000000000 : ℝ)*X 2 0+(2705973081/5000000000 : ℝ)*X 2 1+(-122533127/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081531313/2500000000 : ℝ)*X 0 0+(450407673/1000000000 : ℝ)*X 0 1+(33238459/80000000 : ℝ)*X 0 2+(1081531313/2500000000 : ℝ)*X 1 0+(450407673/1000000000 : ℝ)*X 1 1+(33238459/80000000 : ℝ)*X 1 2+(1081531313/2500000000 : ℝ)*X 2 0+(450407673/1000000000 : ℝ)*X 2 1+(33238459/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1344_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46925282123225970369930993/22212500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (392384223/50000000000000 : ℝ)*(base19) + (77225049/100000000000000 : ℝ)*(base23) + (50093661/100000000000000 : ℝ)*(upper2) + (20994107/100000000000000 : ℝ)*(upper4) + (48629863/100000000000000 : ℝ)*(lower5) + (110013577653961/2500000000000 : ℝ)*(major0) + (110013577653961/2500000000000 : ℝ)*(major1) + (110013577653961/2500000000000 : ℝ)*(major2) + (5958473531668659/100000000000000 : ℝ)*(sp0) + (23275366189521/390625000000 : ℝ)*(sp1) + (5958494452060773/100000000000000 : ℝ)*(sp2) + (2842583577059199/100000000000000 : ℝ)*(sp3) + (20997617163/100000000000000 : ℝ)*(sp4) + (8035553123/100000000000000 : ℝ)*(sp7) + (1421295806306161/50000000000000 : ℝ)*(f.failure) + (2979247264642911/50000000000000 : ℝ)*(f.sum) + (10550323167149/1777000000000000000000000000 : ℝ)*base66 + (252614239865963223/44425000000000000000000000000000 : ℝ)*base67 + (312949990976713223/44425000000000000000000000000000 : ℝ)*base69 + (385040317165538223/44425000000000000000000000000000 : ℝ)*base71 + (1469406504157/444250000000000000000000000 : ℝ)*base73 + (174053115756988223/44425000000000000000000000000000 : ℝ)*base75 + (103753261005163223/44425000000000000000000000000000 : ℝ)*base77 + (146605215291663223/44425000000000000000000000000000 : ℝ)*base79 + (4443151004877/1777000000000000000000000000 : ℝ)*base82 + (3505287/5000000000000000000000 : ℝ)*base90 + (3505287/5000000000000000000000 : ℝ)*base92 + (3505287/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2195022157177392201618470961/888500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62570409/20000000000000 : ℝ)*(base19) + (21179373/4000000000000 : ℝ)*(base23) + (93732307/100000000000000 : ℝ)*(lower1) + (32104769/50000000000000 : ℝ)*(upper3) + (49810627/100000000000000 : ℝ)*(lower4) + (7216891/20000000000000 : ℝ)*(upper5) + (4432318792890509/100000000000000 : ℝ)*(major0) + (4432318792890509/100000000000000 : ℝ)*(major1) + (4432318792890509/100000000000000 : ℝ)*(major2) + (6318119573/100000000000000 : ℝ)*(sp2) + (6001519946995899/100000000000000 : ℝ)*(sp4) + (6001519634143853/100000000000000 : ℝ)*(sp5) + (6001513099392001/100000000000000 : ℝ)*(sp6) + (2863117556435749/100000000000000 : ℝ)*(sp7) + (2863117556435749/100000000000000 : ℝ)*(f.failure) + (6001519946995899/100000000000000 : ℝ)*(f.sum) + (30555966933107/8885000000000000000000000000 : ℝ)*base65 + (12965728002440143013/1777000000000000000000000000000000 : ℝ)*base68 + (5790062403097143013/1777000000000000000000000000000000 : ℝ)*base70 + (34840032454420143013/1777000000000000000000000000000000 : ℝ)*base72 + (11814748513403/2221250000000000000000000000 : ℝ)*base73 + (93048499681445143013/1777000000000000000000000000000000 : ℝ)*base76 + (768194426365856987/1777000000000000000000000000000000 : ℝ)*base77 + (5073803311330856987/1777000000000000000000000000000000 : ℝ)*base79 + (42938118291223/8885000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (32122317/10000000000000000000000 : ℝ)*base89 + (32122317/10000000000000000000000 : ℝ)*base91 + (32122317/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1344_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5577/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2231/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1344_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1344_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2231/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1344_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1344_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1344_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4303/1024 : ℝ) ≤ p) (hpb : p ≤ (269/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154807433/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2231/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1344_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

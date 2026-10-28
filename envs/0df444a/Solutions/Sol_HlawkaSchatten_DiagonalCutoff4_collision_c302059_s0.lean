-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302059_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:22:55.286343+00:00
-- url     : https://prove2.me/submissions/8efceb06-733b-4b27-a063-bf34e46b0c40

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c302059_s0_s0_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3077025497/10000000000 : ℝ)*x 0 + (3077023483/10000000000 : ℝ)*x 1 + (413852093/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3077025497/10000000000 : ℝ)^131 ≤ (4204443446649/20000000000000 : ℝ)^99 := by
    have hnat : (3077025497 : ℕ)^131*20000000000000^99 ≤ 4204443446649^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3077025497 10000000000 4204443446649 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3077023483/10000000000 : ℝ)^131 ≤ (10511099513027/50000000000000 : ℝ)^99 := by
    have hnat : (3077023483 : ℕ)^131*50000000000000^99 ≤ 10511099513027^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3077023483 10000000000 10511099513027 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413852093/625000000 : ℝ)^131 ≤ (7244447965799/12500000000000 : ℝ)^99 := by
    have hnat : (413852093 : ℕ)^131*12500000000000^99 ≤ 7244447965799^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413852093 625000000 7244447965799 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3077025497/10000000000 : ℝ), (3077023483/10000000000 : ℝ), (413852093/625000000 : ℝ)] ![(4204443446649/20000000000000 : ℝ), (10511099513027/50000000000000 : ℝ), (7244447965799/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3077025497/10000000000 : ℝ)|^131 ≤ (4204443446649/20000000000000 : ℝ)^99
        have hw : |(-3077025497/10000000000 : ℝ)|=(3077025497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3077023483/10000000000 : ℝ)|^131 ≤ (10511099513027/50000000000000 : ℝ)^99
        have hw : |(3077023483/10000000000 : ℝ)|=(3077023483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(413852093/625000000 : ℝ)|^131 ≤ (7244447965799/12500000000000 : ℝ)^99
        have hw : |(413852093/625000000 : ℝ)|=(413852093/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s0_s0_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2450809281/10000000000 : ℝ)*x 0 + (137242289/2500000000 : ℝ)*x 1 + (8630686051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2450809281/10000000000 : ℝ)^131 ≤ (777829870049/5000000000000 : ℝ)^99 := by
    have hnat : (2450809281 : ℕ)^131*5000000000000^99 ≤ 777829870049^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2450809281 10000000000 777829870049 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137242289/2500000000 : ℝ)^131 ≤ (2148469030449/100000000000000 : ℝ)^99 := by
    have hnat : (137242289 : ℕ)^131*100000000000000^99 ≤ 2148469030449^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137242289 2500000000 2148469030449 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8630686051/10000000000 : ℝ)^131 ≤ (41147466779003/50000000000000 : ℝ)^99 := by
    have hnat : (8630686051 : ℕ)^131*50000000000000^99 ≤ 41147466779003^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8630686051 10000000000 41147466779003 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2450809281/10000000000 : ℝ), (137242289/2500000000 : ℝ), (8630686051/10000000000 : ℝ)] ![(777829870049/5000000000000 : ℝ), (2148469030449/100000000000000 : ℝ), (41147466779003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2450809281/10000000000 : ℝ)|^131 ≤ (777829870049/5000000000000 : ℝ)^99
        have hw : |(-2450809281/10000000000 : ℝ)|=(2450809281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137242289/2500000000 : ℝ)|^131 ≤ (2148469030449/100000000000000 : ℝ)^99
        have hw : |(137242289/2500000000 : ℝ)|=(137242289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8630686051/10000000000 : ℝ)|^131 ≤ (41147466779003/50000000000000 : ℝ)^99
        have hw : |(8630686051/10000000000 : ℝ)|=(8630686051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s0_s0_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (790085913/10000000000 : ℝ)*x 0 + (-2290765963/10000000000 : ℝ)*x 1 + (863068709/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (790085913/10000000000 : ℝ)^131 ≤ (695659985231/20000000000000 : ℝ)^99 := by
    have hnat : (790085913 : ℕ)^131*20000000000000^99 ≤ 695659985231^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      790085913 10000000000 695659985231 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2290765963/10000000000 : ℝ)^131 ≤ (7113376693471/50000000000000 : ℝ)^99 := by
    have hnat : (2290765963 : ℕ)^131*50000000000000^99 ≤ 7113376693471^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2290765963 10000000000 7113376693471 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (863068709/1000000000 : ℝ)^131 ≤ (10286868333413/12500000000000 : ℝ)^99 := by
    have hnat : (863068709 : ℕ)^131*12500000000000^99 ≤ 10286868333413^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863068709 1000000000 10286868333413 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(790085913/10000000000 : ℝ), (-2290765963/10000000000 : ℝ), (863068709/1000000000 : ℝ)] ![(695659985231/20000000000000 : ℝ), (7113376693471/50000000000000 : ℝ), (10286868333413/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(790085913/10000000000 : ℝ)|^131 ≤ (695659985231/20000000000000 : ℝ)^99
        have hw : |(790085913/10000000000 : ℝ)|=(790085913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2290765963/10000000000 : ℝ)|^131 ≤ (7113376693471/50000000000000 : ℝ)^99
        have hw : |(-2290765963/10000000000 : ℝ)|=(2290765963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(863068709/1000000000 : ℝ)|^131 ≤ (10286868333413/12500000000000 : ℝ)^99
        have hw : |(863068709/1000000000 : ℝ)|=(863068709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s0_s0_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (351058543/1000000000 : ℝ)*x 0 + (25136613/31250000 : ℝ)*x 1 + (-253/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (351058543/1000000000 : ℝ)^131 ≤ (12514154856597/50000000000000 : ℝ)^99 := by
    have hnat : (351058543 : ℕ)^131*50000000000000^99 ≤ 12514154856597^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351058543 1000000000 12514154856597 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25136613/31250000 : ℝ)^131 ≤ (1874292241051/2500000000000 : ℝ)^99 := by
    have hnat : (25136613 : ℕ)^131*2500000000000^99 ≤ 1874292241051^99*31250000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25136613 31250000 1874292241051 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253/400000000 : ℝ)^131 ≤ (313569/50000000000000 : ℝ)^99 := by
    have hnat : (253 : ℕ)^131*50000000000000^99 ≤ 313569^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253 400000000 313569 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(351058543/1000000000 : ℝ), (25136613/31250000 : ℝ), (-253/400000000 : ℝ)] ![(12514154856597/50000000000000 : ℝ), (1874292241051/2500000000000 : ℝ), (313569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(351058543/1000000000 : ℝ)|^131 ≤ (12514154856597/50000000000000 : ℝ)^99
        have hw : |(351058543/1000000000 : ℝ)|=(351058543/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(25136613/31250000 : ℝ)|^131 ≤ (1874292241051/2500000000000 : ℝ)^99
        have hw : |(25136613/31250000 : ℝ)|=(25136613/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-253/400000000 : ℝ)|^131 ≤ (313569/50000000000000 : ℝ)^99
        have hw : |(-253/400000000 : ℝ)|=(253/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s0_s0_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (421335971/2500000000 : ℝ)*x 0 + (33386731/40000000 : ℝ)*x 1 + (397534991/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421335971/2500000000 : ℝ)^131 ≤ (9478274150373/100000000000000 : ℝ)^99 := by
    have hnat : (421335971 : ℕ)^131*100000000000000^99 ≤ 9478274150373^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421335971 2500000000 9478274150373 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33386731/40000000 : ℝ)^131 ≤ (9841349999029/12500000000000 : ℝ)^99 := by
    have hnat : (33386731 : ℕ)^131*12500000000000^99 ≤ 9841349999029^99*40000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33386731 40000000 9841349999029 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397534991/2000000000 : ℝ)^131 ≤ (11790925843889/100000000000000 : ℝ)^99 := by
    have hnat : (397534991 : ℕ)^131*100000000000000^99 ≤ 11790925843889^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397534991 2000000000 11790925843889 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(421335971/2500000000 : ℝ), (33386731/40000000 : ℝ), (397534991/2000000000 : ℝ)] ![(9478274150373/100000000000000 : ℝ), (9841349999029/12500000000000 : ℝ), (11790925843889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(421335971/2500000000 : ℝ)|^131 ≤ (9478274150373/100000000000000 : ℝ)^99
        have hw : |(421335971/2500000000 : ℝ)|=(421335971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33386731/40000000 : ℝ)|^131 ≤ (9841349999029/12500000000000 : ℝ)^99
        have hw : |(33386731/40000000 : ℝ)|=(33386731/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(397534991/2000000000 : ℝ)|^131 ≤ (11790925843889/100000000000000 : ℝ)^99
        have hw : |(397534991/2000000000 : ℝ)|=(397534991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s0_s0_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1208547021/10000000000 : ℝ)*x 0 + (672547593/5000000000 : ℝ)*x 1 + (8990332163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1208547021/10000000000 : ℝ)^131 ≤ (6104097585939/100000000000000 : ℝ)^99 := by
    have hnat : (1208547021 : ℕ)^131*100000000000000^99 ≤ 6104097585939^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208547021 10000000000 6104097585939 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672547593/5000000000 : ℝ)^131 ≤ (439559681221/6250000000000 : ℝ)^99 := by
    have hnat : (672547593 : ℕ)^131*6250000000000^99 ≤ 439559681221^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672547593 5000000000 439559681221 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8990332163/10000000000 : ℝ)^131 ≤ (43431473751409/50000000000000 : ℝ)^99 := by
    have hnat : (8990332163 : ℕ)^131*50000000000000^99 ≤ 43431473751409^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8990332163 10000000000 43431473751409 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1208547021/10000000000 : ℝ), (672547593/5000000000 : ℝ), (8990332163/10000000000 : ℝ)] ![(6104097585939/100000000000000 : ℝ), (439559681221/6250000000000 : ℝ), (43431473751409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1208547021/10000000000 : ℝ)|^131 ≤ (6104097585939/100000000000000 : ℝ)^99
        have hw : |(-1208547021/10000000000 : ℝ)|=(1208547021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(672547593/5000000000 : ℝ)|^131 ≤ (439559681221/6250000000000 : ℝ)^99
        have hw : |(672547593/5000000000 : ℝ)|=(672547593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8990332163/10000000000 : ℝ)|^131 ≤ (43431473751409/50000000000000 : ℝ)^99
        have hw : |(8990332163/10000000000 : ℝ)|=(8990332163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s0_s0_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (146401139/1250000000 : ℝ)*x 0 + (-55233211/400000000 : ℝ)*x 1 + (56189573/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (146401139/1250000000 : ℝ)^131 ≤ (11437129239/195312500000 : ℝ)^99 := by
    have hnat : (146401139 : ℕ)^131*195312500000^99 ≤ 11437129239^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146401139 1250000000 11437129239 195312500000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55233211/400000000 : ℝ)^131 ≤ (7281248481663/100000000000000 : ℝ)^99 := by
    have hnat : (55233211 : ℕ)^131*100000000000000^99 ≤ 7281248481663^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55233211 400000000 7281248481663 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56189573/62500000 : ℝ)^131 ≤ (43431470663873/50000000000000 : ℝ)^99 := by
    have hnat : (56189573 : ℕ)^131*50000000000000^99 ≤ 43431470663873^99*62500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56189573 62500000 43431470663873 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(146401139/1250000000 : ℝ), (-55233211/400000000 : ℝ), (56189573/62500000 : ℝ)] ![(11437129239/195312500000 : ℝ), (7281248481663/100000000000000 : ℝ), (43431470663873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(146401139/1250000000 : ℝ)|^131 ≤ (11437129239/195312500000 : ℝ)^99
        have hw : |(146401139/1250000000 : ℝ)|=(146401139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55233211/400000000 : ℝ)|^131 ≤ (7281248481663/100000000000000 : ℝ)^99
        have hw : |(-55233211/400000000 : ℝ)|=(55233211/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56189573/62500000 : ℝ)|^131 ≤ (43431470663873/50000000000000 : ℝ)^99
        have hw : |(56189573/62500000 : ℝ)|=(56189573/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s0_s0_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (9043180859/10000000000 : ℝ)*x 0 + (2072425851/10000000000 : ℝ)*x 1 + (135291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9043180859/10000000000 : ℝ)^131 ≤ (21884812526321/25000000000000 : ℝ)^99 := by
    have hnat : (9043180859 : ℕ)^131*25000000000000^99 ≤ 21884812526321^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9043180859 10000000000 21884812526321 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2072425851/10000000000 : ℝ)^131 ≤ (6230356889477/50000000000000 : ℝ)^99 := by
    have hnat : (2072425851 : ℕ)^131*50000000000000^99 ≤ 6230356889477^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072425851 10000000000 6230356889477 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135291/10000000000 : ℝ)^131 ≤ (36102531/100000000000000 : ℝ)^99 := by
    have hnat : (135291 : ℕ)^131*100000000000000^99 ≤ 36102531^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135291 10000000000 36102531 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9043180859/10000000000 : ℝ), (2072425851/10000000000 : ℝ), (135291/10000000000 : ℝ)] ![(21884812526321/25000000000000 : ℝ), (6230356889477/50000000000000 : ℝ), (36102531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9043180859/10000000000 : ℝ)|^131 ≤ (21884812526321/25000000000000 : ℝ)^99
        have hw : |(9043180859/10000000000 : ℝ)|=(9043180859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2072425851/10000000000 : ℝ)|^131 ≤ (6230356889477/50000000000000 : ℝ)^99
        have hw : |(2072425851/10000000000 : ℝ)|=(2072425851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135291/10000000000 : ℝ)|^131 ≤ (36102531/100000000000000 : ℝ)^99
        have hw : |(135291/10000000000 : ℝ)|=(135291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s0_s0_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3598368489/5000000000 : ℝ)*x 0 + (1449391111/5000000000 : ℝ)*x 1 + (2487554883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3598368489/5000000000 : ℝ)^131 ≤ (64707891502899/100000000000000 : ℝ)^99 := by
    have hnat : (3598368489 : ℕ)^131*100000000000000^99 ≤ 64707891502899^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3598368489 5000000000 64707891502899 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1449391111/5000000000 : ℝ)^131 ≤ (9713064864281/50000000000000 : ℝ)^99 := by
    have hnat : (1449391111 : ℕ)^131*50000000000000^99 ≤ 9713064864281^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1449391111 5000000000 9713064864281 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2487554883/10000000000 : ℝ)^131 ≤ (7932989373237/50000000000000 : ℝ)^99 := by
    have hnat : (2487554883 : ℕ)^131*50000000000000^99 ≤ 7932989373237^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2487554883 10000000000 7932989373237 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3598368489/5000000000 : ℝ), (1449391111/5000000000 : ℝ), (2487554883/10000000000 : ℝ)] ![(64707891502899/100000000000000 : ℝ), (9713064864281/50000000000000 : ℝ), (7932989373237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3598368489/5000000000 : ℝ)|^131 ≤ (64707891502899/100000000000000 : ℝ)^99
        have hw : |(3598368489/5000000000 : ℝ)|=(3598368489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1449391111/5000000000 : ℝ)|^131 ≤ (9713064864281/50000000000000 : ℝ)^99
        have hw : |(1449391111/5000000000 : ℝ)|=(1449391111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2487554883/10000000000 : ℝ)|^131 ≤ (7932989373237/50000000000000 : ℝ)^99
        have hw : |(2487554883/10000000000 : ℝ)|=(2487554883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s0_s0_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-7284176607/10000000000 : ℝ)*x 0 + (328697793/1250000000 : ℝ)*x 1 + (2641048813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7284176607/10000000000 : ℝ)^131 ≤ (32875123255643/50000000000000 : ℝ)^99 := by
    have hnat : (7284176607 : ℕ)^131*50000000000000^99 ≤ 32875123255643^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7284176607 10000000000 32875123255643 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328697793/1250000000 : ℝ)^131 ≤ (17075578643867/100000000000000 : ℝ)^99 := by
    have hnat : (328697793 : ℕ)^131*100000000000000^99 ≤ 17075578643867^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328697793 1250000000 17075578643867 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641048813/10000000000 : ℝ)^131 ≤ (17174174829227/100000000000000 : ℝ)^99 := by
    have hnat : (2641048813 : ℕ)^131*100000000000000^99 ≤ 17174174829227^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641048813 10000000000 17174174829227 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7284176607/10000000000 : ℝ), (328697793/1250000000 : ℝ), (2641048813/10000000000 : ℝ)] ![(32875123255643/50000000000000 : ℝ), (17075578643867/100000000000000 : ℝ), (17174174829227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7284176607/10000000000 : ℝ)|^131 ≤ (32875123255643/50000000000000 : ℝ)^99
        have hw : |(-7284176607/10000000000 : ℝ)|=(7284176607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328697793/1250000000 : ℝ)|^131 ≤ (17075578643867/100000000000000 : ℝ)^99
        have hw : |(328697793/1250000000 : ℝ)|=(328697793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641048813/10000000000 : ℝ)|^131 ≤ (17174174829227/100000000000000 : ℝ)^99
        have hw : |(2641048813/10000000000 : ℝ)|=(2641048813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s0_s0_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (125659/16000000 : ℝ)*x 0 + (-262117499/10000000000 : ℝ)*x 1 + (310202361/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125659/16000000 : ℝ)^131 ≤ (163943186281/100000000000000 : ℝ)^99 := by
    have hnat : (125659 : ℕ)^131*100000000000000^99 ≤ 163943186281^99*16000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125659 16000000 163943186281 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262117499/10000000000 : ℝ)^131 ≤ (20194951617/2500000000000 : ℝ)^99 := by
    have hnat : (262117499 : ℕ)^131*2500000000000^99 ≤ 20194951617^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262117499 10000000000 20194951617 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310202361/312500000 : ℝ)^131 ≤ (99028258732823/100000000000000 : ℝ)^99 := by
    have hnat : (310202361 : ℕ)^131*100000000000000^99 ≤ 99028258732823^99*312500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310202361 312500000 99028258732823 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(125659/16000000 : ℝ), (-262117499/10000000000 : ℝ), (310202361/312500000 : ℝ)] ![(163943186281/100000000000000 : ℝ), (20194951617/2500000000000 : ℝ), (99028258732823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(125659/16000000 : ℝ)|^131 ≤ (163943186281/100000000000000 : ℝ)^99
        have hw : |(125659/16000000 : ℝ)|=(125659/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-262117499/10000000000 : ℝ)|^131 ≤ (20194951617/2500000000000 : ℝ)^99
        have hw : |(-262117499/10000000000 : ℝ)|=(262117499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(310202361/312500000 : ℝ)|^131 ≤ (99028258732823/100000000000000 : ℝ)^99
        have hw : |(310202361/312500000 : ℝ)|=(310202361/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s0_s0_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8624778007/10000000000 : ℝ)*x 0 + (1350368319/5000000000 : ℝ)*x 1 + (49901609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8624778007/10000000000 : ℝ)^131 ≤ (82220398680033/100000000000000 : ℝ)^99 := by
    have hnat : (8624778007 : ℕ)^131*100000000000000^99 ≤ 82220398680033^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8624778007 10000000000 82220398680033 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350368319/5000000000 : ℝ)^131 ≤ (8844818446691/50000000000000 : ℝ)^99 := by
    have hnat : (1350368319 : ℕ)^131*50000000000000^99 ≤ 8844818446691^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350368319 5000000000 8844818446691 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49901609/10000000000 : ℝ)^131 ≤ (44982208183/50000000000000 : ℝ)^99 := by
    have hnat : (49901609 : ℕ)^131*50000000000000^99 ≤ 44982208183^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49901609 10000000000 44982208183 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8624778007/10000000000 : ℝ), (1350368319/5000000000 : ℝ), (49901609/10000000000 : ℝ)] ![(82220398680033/100000000000000 : ℝ), (8844818446691/50000000000000 : ℝ), (44982208183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8624778007/10000000000 : ℝ)|^131 ≤ (82220398680033/100000000000000 : ℝ)^99
        have hw : |(8624778007/10000000000 : ℝ)|=(8624778007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350368319/5000000000 : ℝ)|^131 ≤ (8844818446691/50000000000000 : ℝ)^99
        have hw : |(1350368319/5000000000 : ℝ)|=(1350368319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(49901609/10000000000 : ℝ)|^131 ≤ (44982208183/50000000000000 : ℝ)^99
        have hw : |(49901609/10000000000 : ℝ)|=(49901609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s0_s0_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (11094329/78125000 : ℝ)*x 0 + (8168805801/10000000000 : ℝ)*x 1 + (498917617/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11094329/78125000 : ℝ)^131 ≤ (7556323259631/100000000000000 : ℝ)^99 := by
    have hnat : (11094329 : ℕ)^131*100000000000000^99 ≤ 7556323259631^99*78125000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11094329 78125000 7556323259631 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8168805801/10000000000 : ℝ)^131 ≤ (76518312303821/100000000000000 : ℝ)^99 := by
    have hnat : (8168805801 : ℕ)^131*100000000000000^99 ≤ 76518312303821^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8168805801 10000000000 76518312303821 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (498917617/2000000000 : ℝ)^131 ≤ (796268220863/5000000000000 : ℝ)^99 := by
    have hnat : (498917617 : ℕ)^131*5000000000000^99 ≤ 796268220863^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498917617 2000000000 796268220863 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(11094329/78125000 : ℝ), (8168805801/10000000000 : ℝ), (498917617/2000000000 : ℝ)] ![(7556323259631/100000000000000 : ℝ), (76518312303821/100000000000000 : ℝ), (796268220863/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(11094329/78125000 : ℝ)|^131 ≤ (7556323259631/100000000000000 : ℝ)^99
        have hw : |(11094329/78125000 : ℝ)|=(11094329/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8168805801/10000000000 : ℝ)|^131 ≤ (76518312303821/100000000000000 : ℝ)^99
        have hw : |(8168805801/10000000000 : ℝ)|=(8168805801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(498917617/2000000000 : ℝ)|^131 ≤ (796268220863/5000000000000 : ℝ)^99
        have hw : |(498917617/2000000000 : ℝ)|=(498917617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302059_s0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : (0 : ℝ) ≤ ((9649/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9649/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48307/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48307/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(45971/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(45971/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (36753/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have s0_pow0 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-3077025497/10000000000 : ℝ)*X 0 0+(3077023483/10000000000 : ℝ)*X 0 1+(413852093/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s0_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2450809281/10000000000 : ℝ)*X 0 0+(137242289/2500000000 : ℝ)*X 0 1+(8630686051/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s0_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((790085913/10000000000 : ℝ)*X 1 0+(-2290765963/10000000000 : ℝ)*X 1 1+(863068709/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s0_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((351058543/1000000000 : ℝ)*X 2 0+(25136613/31250000 : ℝ)*X 2 1+(-253/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s0_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((421335971/2500000000 : ℝ)*X 0 0+(33386731/40000000 : ℝ)*X 0 1+(397534991/2000000000 : ℝ)*X 0 2+(421335971/2500000000 : ℝ)*X 1 0+(33386731/40000000 : ℝ)*X 1 1+(397534991/2000000000 : ℝ)*X 1 2+(421335971/2500000000 : ℝ)*X 2 0+(33386731/40000000 : ℝ)*X 2 1+(397534991/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s0_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1208547021/10000000000 : ℝ)*X 0 0+(672547593/5000000000 : ℝ)*X 0 1+(8990332163/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s0_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((146401139/1250000000 : ℝ)*X 1 0+(-55233211/400000000 : ℝ)*X 1 1+(56189573/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s0_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((9043180859/10000000000 : ℝ)*X 2 0+(2072425851/10000000000 : ℝ)*X 2 1+(135291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s0_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((3598368489/5000000000 : ℝ)*X 0 0+(1449391111/5000000000 : ℝ)*X 0 1+(2487554883/10000000000 : ℝ)*X 0 2+(3598368489/5000000000 : ℝ)*X 1 0+(1449391111/5000000000 : ℝ)*X 1 1+(2487554883/10000000000 : ℝ)*X 1 2+(3598368489/5000000000 : ℝ)*X 2 0+(1449391111/5000000000 : ℝ)*X 2 1+(2487554883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s0_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-7284176607/10000000000 : ℝ)*X 0 0+(328697793/1250000000 : ℝ)*X 0 1+(2641048813/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s0_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((125659/16000000 : ℝ)*X 1 0+(-262117499/10000000000 : ℝ)*X 1 1+(310202361/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s0_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((8624778007/10000000000 : ℝ)*X 2 0+(1350368319/5000000000 : ℝ)*X 2 1+(49901609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s0_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((11094329/78125000 : ℝ)*X 0 0+(8168805801/10000000000 : ℝ)*X 0 1+(498917617/2000000000 : ℝ)*X 0 2+(11094329/78125000 : ℝ)*X 1 0+(8168805801/10000000000 : ℝ)*X 1 1+(498917617/2000000000 : ℝ)*X 1 2+(11094329/78125000 : ℝ)*X 2 0+(8168805801/10000000000 : ℝ)*X 2 1+(498917617/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s0_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((9649/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9649/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3793625550896586925701/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6062376681/125000000000 : ℝ)*(base5) + (941494424629/1000000000000 : ℝ)*(base7) + (124049/100000000000 : ℝ)*(base44) + (73456345679/125000000000 : ℝ)*(base53) + (61355124019/40000000000 : ℝ)*(major_s0_0) + (306775371997/200000000000 : ℝ)*(major_s0_1) + (236556833761/250000000000 : ℝ)*(major_s0_2) + (848471/100000000000 : ℝ)*(sp_s0_0) + (875090959449/1000000000000 : ℝ)*(sp_s0_7) + (875114066433/1000000000000 : ℝ)*(sp_s0_8) + (1511265085803/1000000000000 : ℝ)*(sp_s0_9) + (960626448029/500000000000 : ℝ)*(sp_s0_13) + (3965691/250000000000 : ℝ)*(sp_s0_14) + (4116083/250000000000 : ℝ)*(sp_s0_27) + (10282751897/10000000000 : ℝ)*(f.failure) + (292553214471/200000000000 : ℝ)*(f.sum) + (646573371510057/10000000000000000000000000000 : ℝ)*base62 + (597992522196457/2500000000000000000000000000 : ℝ)*base65 + (1792002153125989/2000000000000000000000000000 : ℝ)*base67 + (915554297168803/2500000000000000000000000000 : ℝ)*base68 + (4782602424889253/10000000000000000000000000000 : ℝ)*base71 + (289260339495403/400000000000000000000000000 : ℝ)*base73 + (764714068166969/2000000000000000000000000000 : ℝ)*base74 + (32627694684137/400000000000000000000000000 : ℝ)*base77 + (32018885950751/500000000000000000000000000 : ℝ)*base79 + (49/100000000000000 : ℝ)*base87 + (49/100000000000000 : ℝ)*base89 + (51/100000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48307/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48307/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (49139036452582975024461/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57636043467/125000000000 : ℝ)*(base5) + (480763542861/500000000000 : ℝ)*(base7) + (1294261/500000000000 : ℝ)*(base33) + (446523408469/1000000000000 : ℝ)*(base53) + (27608720193/250000000000 : ℝ)*(base60) + (302921176509/200000000000 : ℝ)*(major_s0_0) + (1514608471067/1000000000000 : ℝ)*(major_s0_1) + (534042531299/500000000000 : ℝ)*(major_s0_2) + (5489679/1000000000000 : ℝ)*(sp_s0_0) + (2613169/125000000000 : ℝ)*(sp_s0_7) + (489161577641/500000000000 : ℝ)*(sp_s0_14) + (978346961791/1000000000000 : ℝ)*(sp_s0_15) + (471489679499/250000000000 : ℝ)*(sp_s0_16) + (1515796029041/1000000000000 : ℝ)*(sp_s0_20) + (203071458211/200000000000 : ℝ)*(f.failure) + (712436479391/500000000000 : ℝ)*(f.sum) + (224040079658513/10000000000000000000000000000 : ℝ)*base62 + (37310830568763/5000000000000000000000000000 : ℝ)*base65 + (2210837382757421/10000000000000000000000000000 : ℝ)*base66 + (20817691435577/5000000000000000000000000000 : ℝ)*base68 + (942371855970439/10000000000000000000000000000 : ℝ)*base70 + (476194943505467/2000000000000000000000000000 : ℝ)*base72 + (2189093247787359/10000000000000000000000000000 : ℝ)*base74 + (187406587778407/2000000000000000000000000000 : ℝ)*base77 + (107084354178811/2500000000000000000000000000 : ℝ)*base79 + (513/2000000000000000 : ℝ)*base86 + (513/2000000000000000 : ℝ)*base88 + (513/2000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(45971/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(45971/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11249964117245685944151/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84497391289/250000000000 : ℝ)*(base5) + (709482925057/1000000000000 : ℝ)*(base7) + (63598743299/500000000000 : ℝ)*(base33) + (406436349897/500000000000 : ℝ)*(base44) + (105923146713/1000000000000 : ℝ)*(base50) + (1360443860873/1000000000000 : ℝ)*(major_s0_0) + (168692161919/250000000000 : ℝ)*(major_s0_1) + (148764134747/100000000000 : ℝ)*(major_s0_2) + (3628071/200000000000 : ℝ)*(sp_s0_8) + (5589471/1000000000000 : ℝ)*(sp_s0_16) + (1543409002771/1000000000000 : ℝ)*(sp_s0_21) + (24132827041/40000000000 : ℝ)*(sp_s0_22) + (1754195491859/1000000000000 : ℝ)*(sp_s0_23) + (55589983653/100000000000 : ℝ)*(sp_s0_27) + (997279176423/1000000000000 : ℝ)*(f.failure) + (1543409002771/1000000000000 : ℝ)*(f.sum) + (586491692994731/5000000000000000000000000000 : ℝ)*base62 + (157152147777261/1000000000000000000000000000 : ℝ)*base64 + (192531649682297/2500000000000000000000000000 : ℝ)*base66 + (368905895098719/1000000000000000000000000000 : ℝ)*base69 + (356335099208631/10000000000000000000000000000 : ℝ)*base70 + (6843947447118799/10000000000000000000000000000 : ℝ)*base72 + (476613321494163/2500000000000000000000000000 : ℝ)*base74 + (1948042578436021/10000000000000000000000000000 : ℝ)*base76 + (900867385152013/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (8109/10000000000000000 : ℝ)*base86 + (1891/10000000000000000 : ℝ)*base89 + (1891/10000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : (0 : ℝ) ≤ ((9649/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9649/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48307/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48307/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(45971/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(45971/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302059_s0 p hpa hpb X hX

#print axioms solution

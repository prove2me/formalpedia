-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c316054_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:07:13.257986+00:00
-- url     : https://prove2.me/submissions/54aaaf44-abc5-4663-80cd-a426f0940f39

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
theorem collision_support_c316054_s1_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-160078973/2500000000 : ℝ)*x 0 + (2282027699/5000000000 : ℝ)*x 1 + (-3324161607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (160078973/2500000000 : ℝ)^77 ≤ (1556995563427/50000000000000 : ℝ)^61 := by
    have hnat : (160078973 : ℕ)^77*50000000000000^61 ≤ 1556995563427^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160078973 2500000000 1556995563427 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282027699/5000000000 : ℝ)^77 ≤ (7430710150813/20000000000000 : ℝ)^61 := by
    have hnat : (2282027699 : ℕ)^77*20000000000000^61 ≤ 7430710150813^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282027699 5000000000 7430710150813 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3324161607/5000000000 : ℝ)^77 ≤ (3733278631519/6250000000000 : ℝ)^61 := by
    have hnat : (3324161607 : ℕ)^77*6250000000000^61 ≤ 3733278631519^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3324161607 5000000000 3733278631519 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-160078973/2500000000 : ℝ), (2282027699/5000000000 : ℝ), (-3324161607/5000000000 : ℝ)] ![(1556995563427/50000000000000 : ℝ), (7430710150813/20000000000000 : ℝ), (3733278631519/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-160078973/2500000000 : ℝ)|^77 ≤ (1556995563427/50000000000000 : ℝ)^61
        have hw : |(-160078973/2500000000 : ℝ)|=(160078973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2282027699/5000000000 : ℝ)|^77 ≤ (7430710150813/20000000000000 : ℝ)^61
        have hw : |(2282027699/5000000000 : ℝ)|=(2282027699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3324161607/5000000000 : ℝ)|^77 ≤ (3733278631519/6250000000000 : ℝ)^61
        have hw : |(-3324161607/5000000000 : ℝ)|=(3324161607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s1_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (711483951/1250000000 : ℝ)*x 0 + (-92183467/500000000 : ℝ)*x 1 + (-2374789577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (711483951/1250000000 : ℝ)^77 ≤ (49097537466469/100000000000000 : ℝ)^61 := by
    have hnat : (711483951 : ℕ)^77*100000000000000^61 ≤ 49097537466469^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711483951 1250000000 49097537466469 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92183467/500000000 : ℝ)^77 ≤ (1479058383973/12500000000000 : ℝ)^61 := by
    have hnat : (92183467 : ℕ)^77*12500000000000^61 ≤ 1479058383973^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92183467 500000000 1479058383973 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2374789577/5000000000 : ℝ)^77 ≤ (39069995442157/100000000000000 : ℝ)^61 := by
    have hnat : (2374789577 : ℕ)^77*100000000000000^61 ≤ 39069995442157^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2374789577 5000000000 39069995442157 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(711483951/1250000000 : ℝ), (-92183467/500000000 : ℝ), (-2374789577/5000000000 : ℝ)] ![(49097537466469/100000000000000 : ℝ), (1479058383973/12500000000000 : ℝ), (39069995442157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(711483951/1250000000 : ℝ)|^77 ≤ (49097537466469/100000000000000 : ℝ)^61
        have hw : |(711483951/1250000000 : ℝ)|=(711483951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-92183467/500000000 : ℝ)|^77 ≤ (1479058383973/12500000000000 : ℝ)^61
        have hw : |(-92183467/500000000 : ℝ)|=(92183467/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2374789577/5000000000 : ℝ)|^77 ≤ (39069995442157/100000000000000 : ℝ)^61
        have hw : |(-2374789577/5000000000 : ℝ)|=(2374789577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s1_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1329680281/2500000000 : ℝ)*x 0 + (2630422469/5000000000 : ℝ)*x 1 + (167440831/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1329680281/2500000000 : ℝ)^77 ≤ (22535012646039/50000000000000 : ℝ)^61 := by
    have hnat : (1329680281 : ℕ)^77*50000000000000^61 ≤ 22535012646039^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1329680281 2500000000 22535012646039 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630422469/5000000000 : ℝ)^77 ≤ (22225919418383/50000000000000 : ℝ)^61 := by
    have hnat : (2630422469 : ℕ)^77*50000000000000^61 ≤ 22225919418383^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630422469 5000000000 22225919418383 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (167440831/1000000000 : ℝ)^77 ≤ (5239067931203/50000000000000 : ℝ)^61 := by
    have hnat : (167440831 : ℕ)^77*50000000000000^61 ≤ 5239067931203^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167440831 1000000000 5239067931203 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1329680281/2500000000 : ℝ), (2630422469/5000000000 : ℝ), (167440831/1000000000 : ℝ)] ![(22535012646039/50000000000000 : ℝ), (22225919418383/50000000000000 : ℝ), (5239067931203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1329680281/2500000000 : ℝ)|^77 ≤ (22535012646039/50000000000000 : ℝ)^61
        have hw : |(1329680281/2500000000 : ℝ)|=(1329680281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630422469/5000000000 : ℝ)|^77 ≤ (22225919418383/50000000000000 : ℝ)^61
        have hw : |(2630422469/5000000000 : ℝ)|=(2630422469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(167440831/1000000000 : ℝ)|^77 ≤ (5239067931203/50000000000000 : ℝ)^61
        have hw : |(167440831/1000000000 : ℝ)|=(167440831/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s1_s1_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5322720247/10000000000 : ℝ)*x 0 + (5277049927/10000000000 : ℝ)*x 1 + (-1647044099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5322720247/10000000000 : ℝ)^77 ≤ (45112806106657/100000000000000 : ℝ)^61 := by
    have hnat : (5322720247 : ℕ)^77*100000000000000^61 ≤ 45112806106657^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5322720247 10000000000 45112806106657 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5277049927/10000000000 : ℝ)^77 ≤ (44624748448723/100000000000000 : ℝ)^61 := by
    have hnat : (5277049927 : ℕ)^77*100000000000000^61 ≤ 44624748448723^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277049927 10000000000 44624748448723 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1647044099/10000000000 : ℝ)^77 ≤ (2565611357623/25000000000000 : ℝ)^61 := by
    have hnat : (1647044099 : ℕ)^77*25000000000000^61 ≤ 2565611357623^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1647044099 10000000000 2565611357623 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5322720247/10000000000 : ℝ), (5277049927/10000000000 : ℝ), (-1647044099/10000000000 : ℝ)] ![(45112806106657/100000000000000 : ℝ), (44624748448723/100000000000000 : ℝ), (2565611357623/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5322720247/10000000000 : ℝ)|^77 ≤ (45112806106657/100000000000000 : ℝ)^61
        have hw : |(5322720247/10000000000 : ℝ)|=(5322720247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5277049927/10000000000 : ℝ)|^77 ≤ (44624748448723/100000000000000 : ℝ)^61
        have hw : |(5277049927/10000000000 : ℝ)|=(5277049927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1647044099/10000000000 : ℝ)|^77 ≤ (2565611357623/25000000000000 : ℝ)^61
        have hw : |(-1647044099/10000000000 : ℝ)|=(1647044099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s1_s1_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-228906811/5000000000 : ℝ)*x 0 + (772376663/2000000000 : ℝ)*x 1 + (-7356322581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228906811/5000000000 : ℝ)^77 ≤ (203889070661/10000000000000 : ℝ)^61 := by
    have hnat : (228906811 : ℕ)^77*10000000000000^61 ≤ 203889070661^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228906811 5000000000 203889070661 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (772376663/2000000000 : ℝ)^77 ≤ (3761218895219/12500000000000 : ℝ)^61 := by
    have hnat : (772376663 : ℕ)^77*12500000000000^61 ≤ 3761218895219^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772376663 2000000000 3761218895219 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7356322581/10000000000 : ℝ)^77 ≤ (16967839531339/25000000000000 : ℝ)^61 := by
    have hnat : (7356322581 : ℕ)^77*25000000000000^61 ≤ 16967839531339^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7356322581 10000000000 16967839531339 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-228906811/5000000000 : ℝ), (772376663/2000000000 : ℝ), (-7356322581/10000000000 : ℝ)] ![(203889070661/10000000000000 : ℝ), (3761218895219/12500000000000 : ℝ), (16967839531339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-228906811/5000000000 : ℝ)|^77 ≤ (203889070661/10000000000000 : ℝ)^61
        have hw : |(-228906811/5000000000 : ℝ)|=(228906811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(772376663/2000000000 : ℝ)|^77 ≤ (3761218895219/12500000000000 : ℝ)^61
        have hw : |(772376663/2000000000 : ℝ)|=(772376663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7356322581/10000000000 : ℝ)|^77 ≤ (16967839531339/25000000000000 : ℝ)^61
        have hw : |(-7356322581/10000000000 : ℝ)|=(7356322581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s1_s1_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1263643881/2500000000 : ℝ)*x 0 + (-369486091/5000000000 : ℝ)*x 1 + (-6138105189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1263643881/2500000000 : ℝ)^77 ≤ (528290321767/1250000000000 : ℝ)^61 := by
    have hnat : (1263643881 : ℕ)^77*1250000000000^61 ≤ 528290321767^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1263643881 2500000000 528290321767 1250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (369486091/5000000000 : ℝ)^77 ≤ (1865712866319/50000000000000 : ℝ)^61 := by
    have hnat : (369486091 : ℕ)^77*50000000000000^61 ≤ 1865712866319^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369486091 5000000000 1865712866319 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6138105189/10000000000 : ℝ)^77 ≤ (10801069701877/20000000000000 : ℝ)^61 := by
    have hnat : (6138105189 : ℕ)^77*20000000000000^61 ≤ 10801069701877^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6138105189 10000000000 10801069701877 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1263643881/2500000000 : ℝ), (-369486091/5000000000 : ℝ), (-6138105189/10000000000 : ℝ)] ![(528290321767/1250000000000 : ℝ), (1865712866319/50000000000000 : ℝ), (10801069701877/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1263643881/2500000000 : ℝ)|^77 ≤ (528290321767/1250000000000 : ℝ)^61
        have hw : |(1263643881/2500000000 : ℝ)|=(1263643881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-369486091/5000000000 : ℝ)|^77 ≤ (1865712866319/50000000000000 : ℝ)^61
        have hw : |(-369486091/5000000000 : ℝ)|=(369486091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6138105189/10000000000 : ℝ)|^77 ≤ (10801069701877/20000000000000 : ℝ)^61
        have hw : |(-6138105189/10000000000 : ℝ)|=(6138105189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s1_s1_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2270353271/5000000000 : ℝ)*x 0 + (1684729191/2500000000 : ℝ)*x 1 + (31744711/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2270353271/5000000000 : ℝ)^77 ≤ (1153555834429/3125000000000 : ℝ)^61 := by
    have hnat : (2270353271 : ℕ)^77*3125000000000^61 ≤ 1153555834429^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270353271 5000000000 1153555834429 3125000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1684729191/2500000000 : ℝ)^77 ≤ (60761728018929/100000000000000 : ℝ)^61 := by
    have hnat : (1684729191 : ℕ)^77*100000000000000^61 ≤ 60761728018929^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684729191 2500000000 60761728018929 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31744711/625000000 : ℝ)^77 ≤ (145280329589/6250000000000 : ℝ)^61 := by
    have hnat : (31744711 : ℕ)^77*6250000000000^61 ≤ 145280329589^61*625000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31744711 625000000 145280329589 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2270353271/5000000000 : ℝ), (1684729191/2500000000 : ℝ), (31744711/625000000 : ℝ)] ![(1153555834429/3125000000000 : ℝ), (60761728018929/100000000000000 : ℝ), (145280329589/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2270353271/5000000000 : ℝ)|^77 ≤ (1153555834429/3125000000000 : ℝ)^61
        have hw : |(2270353271/5000000000 : ℝ)|=(2270353271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1684729191/2500000000 : ℝ)|^77 ≤ (60761728018929/100000000000000 : ℝ)^61
        have hw : |(1684729191/2500000000 : ℝ)|=(1684729191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31744711/625000000 : ℝ)|^77 ≤ (145280329589/6250000000000 : ℝ)^61
        have hw : |(31744711/625000000 : ℝ)|=(31744711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s1_s1_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1188937329/2500000000 : ℝ)*x 0 + (3293789/5000000 : ℝ)*x 1 + (-41870717/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1188937329/2500000000 : ℝ)^77 ≤ (39134075021181/100000000000000 : ℝ)^61 := by
    have hnat : (1188937329 : ℕ)^77*100000000000000^61 ≤ 39134075021181^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188937329 2500000000 39134075021181 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3293789/5000000 : ℝ)^77 ≤ (59044361645343/100000000000000 : ℝ)^61 := by
    have hnat : (3293789 : ℕ)^77*100000000000000^61 ≤ 59044361645343^61*5000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3293789 5000000 59044361645343 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41870717/1000000000 : ℝ)^77 ≤ (1821563320939/100000000000000 : ℝ)^61 := by
    have hnat : (41870717 : ℕ)^77*100000000000000^61 ≤ 1821563320939^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41870717 1000000000 1821563320939 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1188937329/2500000000 : ℝ), (3293789/5000000 : ℝ), (-41870717/1000000000 : ℝ)] ![(39134075021181/100000000000000 : ℝ), (59044361645343/100000000000000 : ℝ), (1821563320939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1188937329/2500000000 : ℝ)|^77 ≤ (39134075021181/100000000000000 : ℝ)^61
        have hw : |(1188937329/2500000000 : ℝ)|=(1188937329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3293789/5000000 : ℝ)|^77 ≤ (59044361645343/100000000000000 : ℝ)^61
        have hw : |(3293789/5000000 : ℝ)|=(3293789/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41870717/1000000000 : ℝ)|^77 ≤ (1821563320939/100000000000000 : ℝ)^61
        have hw : |(-41870717/1000000000 : ℝ)|=(41870717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s1_s1_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-16877513/10000000000 : ℝ)*x 0 + (2039290123/5000000000 : ℝ)*x 1 + (-7344346111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16877513/10000000000 : ℝ)^77 ≤ (31626060261/100000000000000 : ℝ)^61 := by
    have hnat : (16877513 : ℕ)^77*100000000000000^61 ≤ 31626060261^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16877513 10000000000 31626060261 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2039290123/5000000000 : ℝ)^77 ≤ (8059116788253/25000000000000 : ℝ)^61 := by
    have hnat : (2039290123 : ℕ)^77*25000000000000^61 ≤ 8059116788253^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039290123 5000000000 8059116788253 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7344346111/10000000000 : ℝ)^77 ≤ (33865953388121/50000000000000 : ℝ)^61 := by
    have hnat : (7344346111 : ℕ)^77*50000000000000^61 ≤ 33865953388121^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7344346111 10000000000 33865953388121 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16877513/10000000000 : ℝ), (2039290123/5000000000 : ℝ), (-7344346111/10000000000 : ℝ)] ![(31626060261/100000000000000 : ℝ), (8059116788253/25000000000000 : ℝ), (33865953388121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16877513/10000000000 : ℝ)|^77 ≤ (31626060261/100000000000000 : ℝ)^61
        have hw : |(-16877513/10000000000 : ℝ)|=(16877513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2039290123/5000000000 : ℝ)|^77 ≤ (8059116788253/25000000000000 : ℝ)^61
        have hw : |(2039290123/5000000000 : ℝ)|=(2039290123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7344346111/10000000000 : ℝ)|^77 ≤ (33865953388121/50000000000000 : ℝ)^61
        have hw : |(-7344346111/10000000000 : ℝ)|=(7344346111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s1_s1_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2184607809/5000000000 : ℝ)*x 0 + (-745897481/5000000000 : ℝ)*x 1 + (-157434773/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184607809/5000000000 : ℝ)^77 ≤ (35162769843927/100000000000000 : ℝ)^61 := by
    have hnat : (2184607809 : ℕ)^77*100000000000000^61 ≤ 35162769843927^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184607809 5000000000 35162769843927 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (745897481/5000000000 : ℝ)^77 ≤ (9056848567031/100000000000000 : ℝ)^61 := by
    have hnat : (745897481 : ℕ)^77*100000000000000^61 ≤ 9056848567031^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745897481 5000000000 9056848567031 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157434773/250000000 : ℝ)^77 ≤ (27890190787273/50000000000000 : ℝ)^61 := by
    have hnat : (157434773 : ℕ)^77*50000000000000^61 ≤ 27890190787273^61*250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157434773 250000000 27890190787273 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184607809/5000000000 : ℝ), (-745897481/5000000000 : ℝ), (-157434773/250000000 : ℝ)] ![(35162769843927/100000000000000 : ℝ), (9056848567031/100000000000000 : ℝ), (27890190787273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184607809/5000000000 : ℝ)|^77 ≤ (35162769843927/100000000000000 : ℝ)^61
        have hw : |(2184607809/5000000000 : ℝ)|=(2184607809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-745897481/5000000000 : ℝ)|^77 ≤ (9056848567031/100000000000000 : ℝ)^61
        have hw : |(-745897481/5000000000 : ℝ)|=(745897481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-157434773/250000000 : ℝ)|^77 ≤ (27890190787273/50000000000000 : ℝ)^61
        have hw : |(-157434773/250000000 : ℝ)|=(157434773/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s1_s1_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1742306003/2500000000 : ℝ)*x 0 + (2116053039/5000000000 : ℝ)*x 1 + (593546709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1742306003/2500000000 : ℝ)^77 ≤ (12678925957859/20000000000000 : ℝ)^61 := by
    have hnat : (1742306003 : ℕ)^77*20000000000000^61 ≤ 12678925957859^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742306003 2500000000 12678925957859 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116053039/5000000000 : ℝ)^77 ≤ (2110980300033/6250000000000 : ℝ)^61 := by
    have hnat : (2116053039 : ℕ)^77*6250000000000^61 ≤ 2110980300033^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116053039 5000000000 2110980300033 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (593546709/10000000000 : ℝ)^77 ≤ (707421350169/25000000000000 : ℝ)^61 := by
    have hnat : (593546709 : ℕ)^77*25000000000000^61 ≤ 707421350169^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593546709 10000000000 707421350169 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1742306003/2500000000 : ℝ), (2116053039/5000000000 : ℝ), (593546709/10000000000 : ℝ)] ![(12678925957859/20000000000000 : ℝ), (2110980300033/6250000000000 : ℝ), (707421350169/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1742306003/2500000000 : ℝ)|^77 ≤ (12678925957859/20000000000000 : ℝ)^61
        have hw : |(1742306003/2500000000 : ℝ)|=(1742306003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2116053039/5000000000 : ℝ)|^77 ≤ (2110980300033/6250000000000 : ℝ)^61
        have hw : |(2116053039/5000000000 : ℝ)|=(2116053039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(593546709/10000000000 : ℝ)|^77 ≤ (707421350169/25000000000000 : ℝ)^61
        have hw : |(593546709/10000000000 : ℝ)|=(593546709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s1_s1_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3276593973/5000000000 : ℝ)*x 0 + (4492813819/10000000000 : ℝ)*x 1 + (-460083371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3276593973/5000000000 : ℝ)^77 ≤ (916492838353/1562500000000 : ℝ)^61 := by
    have hnat : (3276593973 : ℕ)^77*1562500000000^61 ≤ 916492838353^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3276593973 5000000000 916492838353 1562500000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492813819/10000000000 : ℝ)^77 ≤ (36422999923119/100000000000000 : ℝ)^61 := by
    have hnat : (4492813819 : ℕ)^77*100000000000000^61 ≤ 36422999923119^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492813819 10000000000 36422999923119 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460083371/5000000000 : ℝ)^77 ≤ (4921458411487/100000000000000 : ℝ)^61 := by
    have hnat : (460083371 : ℕ)^77*100000000000000^61 ≤ 4921458411487^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460083371 5000000000 4921458411487 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3276593973/5000000000 : ℝ), (4492813819/10000000000 : ℝ), (-460083371/5000000000 : ℝ)] ![(916492838353/1562500000000 : ℝ), (36422999923119/100000000000000 : ℝ), (4921458411487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3276593973/5000000000 : ℝ)|^77 ≤ (916492838353/1562500000000 : ℝ)^61
        have hw : |(3276593973/5000000000 : ℝ)|=(3276593973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492813819/10000000000 : ℝ)|^77 ≤ (36422999923119/100000000000000 : ℝ)^61
        have hw : |(4492813819/10000000000 : ℝ)|=(4492813819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-460083371/5000000000 : ℝ)|^77 ≤ (4921458411487/100000000000000 : ℝ)^61
        have hw : |(-460083371/5000000000 : ℝ)|=(460083371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s1_s1_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-7/500000000 : ℝ)*x 0 + (2721670167/5000000000 : ℝ)*x 1 + (-6100939867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7/500000000 : ℝ)^77 ≤ (12193/100000000000000 : ℝ)^61 := by
    have hnat : (7 : ℕ)^77*100000000000000^61 ≤ 12193^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7 500000000 12193 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721670167/5000000000 : ℝ)^77 ≤ (23203543333233/50000000000000 : ℝ)^61 := by
    have hnat : (2721670167 : ℕ)^77*50000000000000^61 ≤ 23203543333233^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721670167 5000000000 23203543333233 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6100939867/10000000000 : ℝ)^77 ≤ (53592913312991/100000000000000 : ℝ)^61 := by
    have hnat : (6100939867 : ℕ)^77*100000000000000^61 ≤ 53592913312991^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6100939867 10000000000 53592913312991 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7/500000000 : ℝ), (2721670167/5000000000 : ℝ), (-6100939867/10000000000 : ℝ)] ![(12193/100000000000000 : ℝ), (23203543333233/50000000000000 : ℝ), (53592913312991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7/500000000 : ℝ)|^77 ≤ (12193/100000000000000 : ℝ)^61
        have hw : |(-7/500000000 : ℝ)|=(7/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721670167/5000000000 : ℝ)|^77 ≤ (23203543333233/50000000000000 : ℝ)^61
        have hw : |(2721670167/5000000000 : ℝ)|=(2721670167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6100939867/10000000000 : ℝ)|^77 ≤ (53592913312991/100000000000000 : ℝ)^61
        have hw : |(-6100939867/10000000000 : ℝ)|=(6100939867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s1_s1_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6692184673/10000000000 : ℝ)*x 0 + (-332169223/2500000000 : ℝ)*x 1 + (-404928349/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6692184673/10000000000 : ℝ)^77 ≤ (60230329551961/100000000000000 : ℝ)^61 := by
    have hnat : (6692184673 : ℕ)^77*100000000000000^61 ≤ 60230329551961^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6692184673 10000000000 60230329551961 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (332169223/2500000000 : ℝ)^77 ≤ (7825220731989/100000000000000 : ℝ)^61 := by
    have hnat : (332169223 : ℕ)^77*100000000000000^61 ≤ 7825220731989^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332169223 2500000000 7825220731989 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (404928349/1000000000 : ℝ)^77 ≤ (1277777987939/4000000000000 : ℝ)^61 := by
    have hnat : (404928349 : ℕ)^77*4000000000000^61 ≤ 1277777987939^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404928349 1000000000 1277777987939 4000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6692184673/10000000000 : ℝ), (-332169223/2500000000 : ℝ), (-404928349/1000000000 : ℝ)] ![(60230329551961/100000000000000 : ℝ), (7825220731989/100000000000000 : ℝ), (1277777987939/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6692184673/10000000000 : ℝ)|^77 ≤ (60230329551961/100000000000000 : ℝ)^61
        have hw : |(6692184673/10000000000 : ℝ)|=(6692184673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-332169223/2500000000 : ℝ)|^77 ≤ (7825220731989/100000000000000 : ℝ)^61
        have hw : |(-332169223/2500000000 : ℝ)|=(332169223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-404928349/1000000000 : ℝ)|^77 ≤ (1277777987939/4000000000000 : ℝ)^61
        have hw : |(-404928349/1000000000 : ℝ)|=(404928349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s1_s1_23 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (603486081/1250000000 : ℝ)*x 0 + (1398650473/2500000000 : ℝ)*x 1 + (1873459001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (603486081/1250000000 : ℝ)^77 ≤ (39884883278381/100000000000000 : ℝ)^61 := by
    have hnat : (603486081 : ℕ)^77*100000000000000^61 ≤ 39884883278381^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603486081 1250000000 39884883278381 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1398650473/2500000000 : ℝ)^77 ≤ (24020403066403/50000000000000 : ℝ)^61 := by
    have hnat : (1398650473 : ℕ)^77*50000000000000^61 ≤ 24020403066403^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398650473 2500000000 24020403066403 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873459001/10000000000 : ℝ)^77 ≤ (3018577643031/25000000000000 : ℝ)^61 := by
    have hnat : (1873459001 : ℕ)^77*25000000000000^61 ≤ 3018577643031^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873459001 10000000000 3018577643031 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(603486081/1250000000 : ℝ), (1398650473/2500000000 : ℝ), (1873459001/10000000000 : ℝ)] ![(39884883278381/100000000000000 : ℝ), (24020403066403/50000000000000 : ℝ), (3018577643031/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(603486081/1250000000 : ℝ)|^77 ≤ (39884883278381/100000000000000 : ℝ)^61
        have hw : |(603486081/1250000000 : ℝ)|=(603486081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1398650473/2500000000 : ℝ)|^77 ≤ (24020403066403/50000000000000 : ℝ)^61
        have hw : |(1398650473/2500000000 : ℝ)|=(1398650473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1873459001/10000000000 : ℝ)|^77 ≤ (3018577643031/25000000000000 : ℝ)^61
        have hw : |(1873459001/10000000000 : ℝ)|=(1873459001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316054_s1_s1_27 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1552006537/2500000000 : ℝ)*x 0 + (443768289/1000000000 : ℝ)*x 1 + (-1530854811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1552006537/2500000000 : ℝ)^77 ≤ (2739152885133/5000000000000 : ℝ)^61 := by
    have hnat : (1552006537 : ℕ)^77*5000000000000^61 ≤ 2739152885133^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552006537 2500000000 2739152885133 5000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443768289/1000000000 : ℝ)^77 ≤ (7171947210529/20000000000000 : ℝ)^61 := by
    have hnat : (443768289 : ℕ)^77*20000000000000^61 ≤ 7171947210529^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443768289 1000000000 7171947210529 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1530854811/10000000000 : ℝ)^77 ≤ (2339301555867/25000000000000 : ℝ)^61 := by
    have hnat : (1530854811 : ℕ)^77*25000000000000^61 ≤ 2339301555867^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1530854811 10000000000 2339301555867 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1552006537/2500000000 : ℝ), (443768289/1000000000 : ℝ), (-1530854811/10000000000 : ℝ)] ![(2739152885133/5000000000000 : ℝ), (7171947210529/20000000000000 : ℝ), (2339301555867/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1552006537/2500000000 : ℝ)|^77 ≤ (2739152885133/5000000000000 : ℝ)^61
        have hw : |(1552006537/2500000000 : ℝ)|=(1552006537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(443768289/1000000000 : ℝ)|^77 ≤ (7171947210529/20000000000000 : ℝ)^61
        have hw : |(443768289/1000000000 : ℝ)|=(443768289/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1530854811/10000000000 : ℝ)|^77 ≤ (2339301555867/25000000000000 : ℝ)^61
        have hw : |(-1530854811/10000000000 : ℝ)|=(1530854811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316054_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((37481/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37481/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3929/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3929/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-693/1000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-693/1000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6401/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6401/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(54153/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(54153/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42163/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42163/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (173433/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (37481/50000 : ℝ) ^ (19/4 : ℝ) ≤ (25438736345396872863/100000000000000000000 : ℝ) := by
    have hpowers : (37481/50000 : ℝ)^19 ≤ (25438736345396872863/100000000000000000000 : ℝ)^4 := by
      have hnat : (37481 : ℕ)^19*100000000000000000000^4 ≤ 25438736345396872863^4*50000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37481 50000 25438736345396872863 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37481/50000 : ℝ)) (X := (25438736345396872863/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (125438736345396872863/100000000000000000000 : ℝ) ≤ (2097743830878601/2000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (125438736345396872863/100000000000000000000 : ℝ)^4 ≤ (2097743830878601/2000000000000000 : ℝ)^19 := by
      have hnat : (125438736345396872863 : ℕ)^4*2000000000000000^19 ≤ 2097743830878601^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125438736345396872863 100000000000000000000 2097743830878601 2000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2097743830878601/2000000000000000 : ℝ)) (X := (125438736345396872863/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (75438736345396872863/50000000000000000000 : ℝ) ≤ (10904484436793889/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (75438736345396872863/50000000000000000000 : ℝ)^4 ≤ (10904484436793889/10000000000000000 : ℝ)^19 := by
      have hnat : (75438736345396872863 : ℕ)^4*10000000000000000^19 ≤ 10904484436793889^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75438736345396872863 50000000000000000000 10904484436793889 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10904484436793889/10000000000000000 : ℝ)) (X := (75438736345396872863/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(97743830878601/1499240000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(103941320600221/1874050000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (37481/50000 : ℝ)) (alpha := (97743830878601/1499240000000000 : ℝ)) (beta := (103941320600221/1874050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (37481/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(97743830878601/1499240000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(103941320600221/1874050000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (3929/5000 : ℝ) ^ (19/4 : ℝ) ≤ (15911170171886890473/50000000000000000000 : ℝ) := by
    have hpowers : (3929/5000 : ℝ)^19 ≤ (15911170171886890473/50000000000000000000 : ℝ)^4 := by
      have hnat : (3929 : ℕ)^19*50000000000000000000^4 ≤ 15911170171886890473^4*5000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3929 5000 15911170171886890473 50000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3929/5000 : ℝ)) (X := (15911170171886890473/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (65911170171886890473/50000000000000000000 : ℝ) ≤ (10598901249740991/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (65911170171886890473/50000000000000000000 : ℝ)^4 ≤ (10598901249740991/10000000000000000 : ℝ)^19 := by
      have hnat : (65911170171886890473 : ℕ)^4*10000000000000000^19 ≤ 10598901249740991^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65911170171886890473 50000000000000000000 10598901249740991 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10598901249740991/10000000000000000 : ℝ)) (X := (65911170171886890473/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (40911170171886890473/25000000000000000000 : ℝ) ≤ (5546282438844103/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (40911170171886890473/25000000000000000000 : ℝ)^4 ≤ (5546282438844103/5000000000000000 : ℝ)^19 := by
      have hnat : (40911170171886890473 : ℕ)^4*5000000000000000^19 ≤ 5546282438844103^19*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40911170171886890473 25000000000000000000 5546282438844103 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5546282438844103/5000000000000000 : ℝ)) (X := (40911170171886890473/25000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(598901249740991/7858000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(98732725589443/1571600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (3929/5000 : ℝ)) (alpha := (598901249740991/7858000000000000 : ℝ)) (beta := (98732725589443/1571600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (3929/5000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(598901249740991/7858000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(98732725589443/1571600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (693/1000 : ℝ) ^ (19/4 : ℝ) ≤ (17517933138022272863/100000000000000000000 : ℝ) := by
    have hpowers : (693/1000 : ℝ)^19 ≤ (17517933138022272863/100000000000000000000 : ℝ)^4 := by
      have hnat : (693 : ℕ)^19*100000000000000000000^4 ≤ 17517933138022272863^4*1000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        693 1000 17517933138022272863 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (693/1000 : ℝ)) (X := (17517933138022272863/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (117517933138022272863/100000000000000000000 : ℝ) ≤ (10345673474746589/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (117517933138022272863/100000000000000000000 : ℝ)^4 ≤ (10345673474746589/10000000000000000 : ℝ)^19 := by
      have hnat : (117517933138022272863 : ℕ)^4*10000000000000000^19 ≤ 10345673474746589^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        117517933138022272863 100000000000000000000 10345673474746589 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10345673474746589/10000000000000000 : ℝ)) (X := (117517933138022272863/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (67517933138022272863/50000000000000000000 : ℝ) ≤ (1065278043275769/1000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (67517933138022272863/50000000000000000000 : ℝ)^4 ≤ (1065278043275769/1000000000000000 : ℝ)^19 := by
      have hnat : (67517933138022272863 : ℕ)^4*1000000000000000^19 ≤ 1065278043275769^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67517933138022272863 50000000000000000000 1065278043275769 1000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1065278043275769/1000000000000000 : ℝ)) (X := (67517933138022272863/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(31424861340599/630000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(307106958011101/6930000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (693/1000 : ℝ)) (alpha := (31424861340599/630000000000000 : ℝ)) (beta := (307106958011101/6930000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (693/1000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(31424861340599/630000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(307106958011101/6930000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-160078973/2500000000 : ℝ)*X 0 0+(2282027699/5000000000 : ℝ)*X 0 1+(-3324161607/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((711483951/1250000000 : ℝ)*X 1 0+(-92183467/500000000 : ℝ)*X 1 1+(-2374789577/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1329680281/2500000000 : ℝ)*X 2 0+(2630422469/5000000000 : ℝ)*X 2 1+(167440831/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5322720247/10000000000 : ℝ)*X 0 0+(5277049927/10000000000 : ℝ)*X 0 1+(-1647044099/10000000000 : ℝ)*X 0 2+(5322720247/10000000000 : ℝ)*X 1 0+(5277049927/10000000000 : ℝ)*X 1 1+(-1647044099/10000000000 : ℝ)*X 1 2+(5322720247/10000000000 : ℝ)*X 2 0+(5277049927/10000000000 : ℝ)*X 2 1+(-1647044099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-228906811/5000000000 : ℝ)*X 0 0+(772376663/2000000000 : ℝ)*X 0 1+(-7356322581/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1263643881/2500000000 : ℝ)*X 1 0+(-369486091/5000000000 : ℝ)*X 1 1+(-6138105189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2270353271/5000000000 : ℝ)*X 2 0+(1684729191/2500000000 : ℝ)*X 2 1+(31744711/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1188937329/2500000000 : ℝ)*X 0 0+(3293789/5000000 : ℝ)*X 0 1+(-41870717/1000000000 : ℝ)*X 0 2+(1188937329/2500000000 : ℝ)*X 1 0+(3293789/5000000 : ℝ)*X 1 1+(-41870717/1000000000 : ℝ)*X 1 2+(1188937329/2500000000 : ℝ)*X 2 0+(3293789/5000000 : ℝ)*X 2 1+(-41870717/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-16877513/10000000000 : ℝ)*X 0 0+(2039290123/5000000000 : ℝ)*X 0 1+(-7344346111/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2184607809/5000000000 : ℝ)*X 1 0+(-745897481/5000000000 : ℝ)*X 1 1+(-157434773/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1742306003/2500000000 : ℝ)*X 2 0+(2116053039/5000000000 : ℝ)*X 2 1+(593546709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3276593973/5000000000 : ℝ)*X 0 0+(4492813819/10000000000 : ℝ)*X 0 1+(-460083371/5000000000 : ℝ)*X 0 2+(3276593973/5000000000 : ℝ)*X 1 0+(4492813819/10000000000 : ℝ)*X 1 1+(-460083371/5000000000 : ℝ)*X 1 2+(3276593973/5000000000 : ℝ)*X 2 0+(4492813819/10000000000 : ℝ)*X 2 1+(-460083371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-7/500000000 : ℝ)*X 0 0+(2721670167/5000000000 : ℝ)*X 0 1+(-6100939867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((6692184673/10000000000 : ℝ)*X 1 0+(-332169223/2500000000 : ℝ)*X 1 1+(-404928349/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((603486081/1250000000 : ℝ)*X 2 0+(1398650473/2500000000 : ℝ)*X 2 1+(1873459001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1552006537/2500000000 : ℝ)*X 0 0+(443768289/1000000000 : ℝ)*X 0 1+(-1530854811/10000000000 : ℝ)*X 0 2+(1552006537/2500000000 : ℝ)*X 1 0+(443768289/1000000000 : ℝ)*X 1 1+(-1530854811/10000000000 : ℝ)*X 1 2+(1552006537/2500000000 : ℝ)*X 2 0+(443768289/1000000000 : ℝ)*X 2 1+(-1530854811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316054_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((6401/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6401/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (398452441520443054303053/34378750000000000000000000000 : ℝ) := by norm_num
    linear_combination (155506417971/1000000000000 : ℝ)*(base7) + (37408851249/200000000000 : ℝ)*(base39) + (345419567617/1000000000000 : ℝ)*(base60) + (3496240375749/1000000000000 : ℝ)*(major_s1_0) + (3496240375749/1000000000000 : ℝ)*(major_s1_1) + (3496240375749/1000000000000 : ℝ)*(major_s1_2) + (736699/1000000000000 : ℝ)*(sp_s1_0) + (1232502974229/250000000000 : ℝ)*(sp_s1_7) + (4930156710907/1000000000000 : ℝ)*(sp_s1_8) + (49301619399/10000000000 : ℝ)*(sp_s1_9) + (1063959783549/500000000000 : ℝ)*(sp_s1_13) + (9455631/62500000000 : ℝ)*(sp_s1_14) + (1803201/250000000000 : ℝ)*(sp_s1_22) + (1983811/1000000000000 : ℝ)*(sp_s1_23) + (1972413149127/1000000000000 : ℝ)*(f.failure) + (4930163923711/1000000000000 : ℝ)*(f.sum) + (12051373091491149/68757500000000000000000000000 : ℝ)*base63 + (12078414849451/70000000000000000000000000 : ℝ)*base65 + (556730996216127/1571600000000000000000000000 : ℝ)*base66 + (35546926007739/70000000000000000000000000 : ℝ)*base69 + (261794452620016319/2623670000000000000000000000000 : ℝ)*base70 + (51823259503257/234256250000000000000000000 : ℝ)*base72 + (2600511068630459/7858000000000000000000000000 : ℝ)*base75 + (453404777096061/1499240000000000000000000000 : ℝ)*base77 + (3488177016644171401/58905139600000000000000000000000 : ℝ)*base79 + (95361/100000000000000000 : ℝ)*base86 + (95361/100000000000000000 : ℝ)*base88 + (95361/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(54153/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(54153/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34589339432369354130743327717/7731299572500000000000000000000000 : ℝ) := by norm_num
    linear_combination (400812738209/1000000000000 : ℝ)*(base7) + (73644475337/1000000000000 : ℝ)*(base39) + (38509/500000000000 : ℝ)*(base49) + (3055593553051/1000000000000 : ℝ)*(major_s1_0) + (3055593553051/1000000000000 : ℝ)*(major_s1_1) + (3055593553051/1000000000000 : ℝ)*(major_s1_2) + (1499549/125000000000 : ℝ)*(sp_s1_1) + (8719127/1000000000000 : ℝ)*(sp_s1_2) + (3934933/200000000000 : ℝ)*(sp_s1_8) + (1038912572727/250000000000 : ℝ)*(sp_s1_14) + (1038904749909/250000000000 : ℝ)*(sp_s1_15) + (2077820975783/500000000000 : ℝ)*(sp_s1_16) + (2124633830211/1000000000000 : ℝ)*(sp_s1_20) + (189893/500000000000 : ℝ)*(sp_s1_21) + (861910546001/500000000000 : ℝ)*(f.failure) + (4155650670693/1000000000000 : ℝ)*(f.sum) + (106349495272010359/618817500000000000000000000000 : ℝ)*base63 + (1333988056373849/6930000000000000000000000000 : ℝ)*base64 + (401322427213327/1571600000000000000000000000 : ℝ)*base67 + (195824651267549/630000000000000000000000000 : ℝ)*base69 + (36453924538313123381/259743330000000000000000000000000 : ℝ)*base71 + (542744689276527/937025000000000000000000000 : ℝ)*base72 + (3283945900686741/7858000000000000000000000000 : ℝ)*base75 + (355448376625959/1499240000000000000000000000 : ℝ)*base77 + (36393631226301444081/58905139600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (50743/50000000000000000 : ℝ)*base86 + (50743/50000000000000000 : ℝ)*base88 + (50743/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42163/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42163/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (237897687577641954140031111/14726284900000000000000000000000 : ℝ) := by norm_num
    linear_combination (16906597491/50000000000 : ℝ)*(base7) + (873703/1000000000000 : ℝ)*(base15) + (581369863133/1000000000000 : ℝ)*(base39) + (1762552013577/500000000000 : ℝ)*(major_s1_0) + (1762552013577/500000000000 : ℝ)*(major_s1_1) + (1762552013577/500000000000 : ℝ)*(major_s1_2) + (1461773/12500000000 : ℝ)*(sp_s1_2) + (8117127/250000000000 : ℝ)*(sp_s1_6) + (66367/2000000000 : ℝ)*(sp_s1_9) + (7117517/62500000000 : ℝ)*(sp_s1_20) + (2433014277191/500000000000 : ℝ)*(sp_s1_21) + (4866027680679/1000000000000 : ℝ)*(sp_s1_22) + (2432939214521/500000000000 : ℝ)*(sp_s1_23) + (1163341127287/500000000000 : ℝ)*(sp_s1_27) + (994348326767/500000000000 : ℝ)*(f.failure) + (2433014277191/500000000000 : ℝ)*(f.sum) + (1235333818145831/103136250000000000000000000000 : ℝ)*base63 + (698224205673241/1155000000000000000000000000 : ℝ)*base64 + (500978629882309/785800000000000000000000000 : ℝ)*base67 + (65829668985959/105000000000000000000000000 : ℝ)*base68 + (382059233444583829/43290555000000000000000000000000 : ℝ)*base71 + (687701563141867/937025000000000000000000000 : ℝ)*base73 + (2036503403741593/3929000000000000000000000000 : ℝ)*base74 + (498766513004959/749620000000000000000000000 : ℝ)*base76 + (7027277267614834693/29452569800000000000000000000000 : ℝ)*base79 + (38119/50000000000000000 : ℝ)*base87 + (38119/50000000000000000 : ℝ)*base89 + (38119/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((37481/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37481/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3929/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3929/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-693/1000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-693/1000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6401/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6401/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(54153/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(54153/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42163/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42163/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c316054_s1 p hpa hpb X hX hprev0

#print axioms solution

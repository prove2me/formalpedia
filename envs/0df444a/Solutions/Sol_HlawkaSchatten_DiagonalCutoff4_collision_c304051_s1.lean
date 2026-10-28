-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304051_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:41:17.114708+00:00
-- url     : https://prove2.me/submissions/73e65154-9282-4be1-a509-55aaf46f82d0

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
theorem collision_support_c304051_s1_s1_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3660542971/10000000000 : ℝ)*x 0 + (1822528519/5000000000 : ℝ)*x 1 + (5559804809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3660542971/10000000000 : ℝ)^17 ≤ (5373803917979/20000000000000 : ℝ)^13 := by
    have hnat : (3660542971 : ℕ)^17*20000000000000^13 ≤ 5373803917979^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3660542971 10000000000 5373803917979 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1822528519/5000000000 : ℝ)^17 ≤ (26720471788633/100000000000000 : ℝ)^13 := by
    have hnat : (1822528519 : ℕ)^17*100000000000000^13 ≤ 26720471788633^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1822528519 5000000000 26720471788633 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5559804809/10000000000 : ℝ)^17 ≤ (2320525430611/5000000000000 : ℝ)^13 := by
    have hnat : (5559804809 : ℕ)^17*5000000000000^13 ≤ 2320525430611^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5559804809 10000000000 2320525430611 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3660542971/10000000000 : ℝ), (1822528519/5000000000 : ℝ), (5559804809/10000000000 : ℝ)] ![(5373803917979/20000000000000 : ℝ), (26720471788633/100000000000000 : ℝ), (2320525430611/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3660542971/10000000000 : ℝ)|^17 ≤ (5373803917979/20000000000000 : ℝ)^13
        have hw : |(-3660542971/10000000000 : ℝ)|=(3660542971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1822528519/5000000000 : ℝ)|^17 ≤ (26720471788633/100000000000000 : ℝ)^13
        have hw : |(1822528519/5000000000 : ℝ)|=(1822528519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5559804809/10000000000 : ℝ)|^17 ≤ (2320525430611/5000000000000 : ℝ)^13
        have hw : |(5559804809/10000000000 : ℝ)|=(5559804809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304051_s1_s1_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2619449663/10000000000 : ℝ)*x 0 + (-2608368077/10000000000 : ℝ)*x 1 + (3613779577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2619449663/10000000000 : ℝ)^17 ≤ (1084121068441/6250000000000 : ℝ)^13 := by
    have hnat : (2619449663 : ℕ)^17*6250000000000^13 ≤ 1084121068441^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619449663 10000000000 1084121068441 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608368077/10000000000 : ℝ)^17 ≤ (1725003851593/10000000000000 : ℝ)^13 := by
    have hnat : (2608368077 : ℕ)^17*10000000000000^13 ≤ 1725003851593^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608368077 10000000000 1725003851593 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3613779577/5000000000 : ℝ)^17 ≤ (1308080487493/2000000000000 : ℝ)^13 := by
    have hnat : (3613779577 : ℕ)^17*2000000000000^13 ≤ 1308080487493^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3613779577 5000000000 1308080487493 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2619449663/10000000000 : ℝ), (-2608368077/10000000000 : ℝ), (3613779577/5000000000 : ℝ)] ![(1084121068441/6250000000000 : ℝ), (1725003851593/10000000000000 : ℝ), (1308080487493/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2619449663/10000000000 : ℝ)|^17 ≤ (1084121068441/6250000000000 : ℝ)^13
        have hw : |(2619449663/10000000000 : ℝ)|=(2619449663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2608368077/10000000000 : ℝ)|^17 ≤ (1725003851593/10000000000000 : ℝ)^13
        have hw : |(-2608368077/10000000000 : ℝ)|=(2608368077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3613779577/5000000000 : ℝ)|^17 ≤ (1308080487493/2000000000000 : ℝ)^13
        have hw : |(3613779577/5000000000 : ℝ)|=(3613779577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304051_s1_s1_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2832463269/5000000000 : ℝ)*x 0 + (2841559749/5000000000 : ℝ)*x 1 + (-240375727/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2832463269/5000000000 : ℝ)^17 ≤ (23780668880707/50000000000000 : ℝ)^13 := by
    have hnat : (2832463269 : ℕ)^17*50000000000000^13 ≤ 23780668880707^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2832463269 5000000000 23780668880707 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2841559749/5000000000 : ℝ)^17 ≤ (23880589031547/50000000000000 : ℝ)^13 := by
    have hnat : (2841559749 : ℕ)^17*50000000000000^13 ≤ 23880589031547^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2841559749 5000000000 23880589031547 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240375727/2500000000 : ℝ)^17 ≤ (4677484163451/100000000000000 : ℝ)^13 := by
    have hnat : (240375727 : ℕ)^17*100000000000000^13 ≤ 4677484163451^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240375727 2500000000 4677484163451 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2832463269/5000000000 : ℝ), (2841559749/5000000000 : ℝ), (-240375727/2500000000 : ℝ)] ![(23780668880707/50000000000000 : ℝ), (23880589031547/50000000000000 : ℝ), (4677484163451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2832463269/5000000000 : ℝ)|^17 ≤ (23780668880707/50000000000000 : ℝ)^13
        have hw : |(2832463269/5000000000 : ℝ)|=(2832463269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2841559749/5000000000 : ℝ)|^17 ≤ (23880589031547/50000000000000 : ℝ)^13
        have hw : |(2841559749/5000000000 : ℝ)|=(2841559749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-240375727/2500000000 : ℝ)|^17 ≤ (4677484163451/100000000000000 : ℝ)^13
        have hw : |(-240375727/2500000000 : ℝ)|=(240375727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304051_s1_s1_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-62397553/200000000 : ℝ)*x 0 + (2734946993/10000000000 : ℝ)*x 1 + (6752979447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62397553/200000000 : ℝ)^17 ≤ (2180156059521/10000000000000 : ℝ)^13 := by
    have hnat : (62397553 : ℕ)^17*10000000000000^13 ≤ 2180156059521^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62397553 200000000 2180156059521 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734946993/10000000000 : ℝ)^17 ≤ (9176401975341/50000000000000 : ℝ)^13 := by
    have hnat : (2734946993 : ℕ)^17*50000000000000^13 ≤ 9176401975341^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734946993 10000000000 9176401975341 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6752979447/10000000000 : ℝ)^17 ≤ (59845635440341/100000000000000 : ℝ)^13 := by
    have hnat : (6752979447 : ℕ)^17*100000000000000^13 ≤ 59845635440341^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6752979447 10000000000 59845635440341 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-62397553/200000000 : ℝ), (2734946993/10000000000 : ℝ), (6752979447/10000000000 : ℝ)] ![(2180156059521/10000000000000 : ℝ), (9176401975341/50000000000000 : ℝ), (59845635440341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-62397553/200000000 : ℝ)|^17 ≤ (2180156059521/10000000000000 : ℝ)^13
        have hw : |(-62397553/200000000 : ℝ)|=(62397553/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734946993/10000000000 : ℝ)|^17 ≤ (9176401975341/50000000000000 : ℝ)^13
        have hw : |(2734946993/10000000000 : ℝ)|=(2734946993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6752979447/10000000000 : ℝ)|^17 ≤ (59845635440341/100000000000000 : ℝ)^13
        have hw : |(6752979447/10000000000 : ℝ)|=(6752979447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304051_s1_s1_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1916724611/10000000000 : ℝ)*x 0 + (-840119517/5000000000 : ℝ)*x 1 + (2082884031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1916724611/10000000000 : ℝ)^17 ≤ (11529457259283/100000000000000 : ℝ)^13 := by
    have hnat : (1916724611 : ℕ)^17*100000000000000^13 ≤ 11529457259283^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916724611 10000000000 11529457259283 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (840119517/5000000000 : ℝ)^17 ≤ (9705629451849/100000000000000 : ℝ)^13 := by
    have hnat : (840119517 : ℕ)^17*100000000000000^13 ≤ 9705629451849^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840119517 5000000000 9705629451849 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2082884031/2500000000 : ℝ)^17 ≤ (78764913267973/100000000000000 : ℝ)^13 := by
    have hnat : (2082884031 : ℕ)^17*100000000000000^13 ≤ 78764913267973^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082884031 2500000000 78764913267973 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1916724611/10000000000 : ℝ), (-840119517/5000000000 : ℝ), (2082884031/2500000000 : ℝ)] ![(11529457259283/100000000000000 : ℝ), (9705629451849/100000000000000 : ℝ), (78764913267973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1916724611/10000000000 : ℝ)|^17 ≤ (11529457259283/100000000000000 : ℝ)^13
        have hw : |(1916724611/10000000000 : ℝ)|=(1916724611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-840119517/5000000000 : ℝ)|^17 ≤ (9705629451849/100000000000000 : ℝ)^13
        have hw : |(-840119517/5000000000 : ℝ)|=(840119517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2082884031/2500000000 : ℝ)|^17 ≤ (78764913267973/100000000000000 : ℝ)^13
        have hw : |(2082884031/2500000000 : ℝ)|=(2082884031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304051_s1_s1_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2309607683/5000000000 : ℝ)*x 0 + (3525519041/5000000000 : ℝ)*x 1 + (-52033217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2309607683/5000000000 : ℝ)^17 ≤ (2276346905713/6250000000000 : ℝ)^13 := by
    have hnat : (2309607683 : ℕ)^17*6250000000000^13 ≤ 2276346905713^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2309607683 5000000000 2276346905713 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3525519041/5000000000 : ℝ)^17 ≤ (12664606191453/20000000000000 : ℝ)^13 := by
    have hnat : (3525519041 : ℕ)^17*20000000000000^13 ≤ 12664606191453^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3525519041 5000000000 12664606191453 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52033217/5000000000 : ℝ)^17 ≤ (997728673/390625000000 : ℝ)^13 := by
    have hnat : (52033217 : ℕ)^17*390625000000^13 ≤ 997728673^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52033217 5000000000 997728673 390625000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2309607683/5000000000 : ℝ), (3525519041/5000000000 : ℝ), (-52033217/5000000000 : ℝ)] ![(2276346905713/6250000000000 : ℝ), (12664606191453/20000000000000 : ℝ), (997728673/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2309607683/5000000000 : ℝ)|^17 ≤ (2276346905713/6250000000000 : ℝ)^13
        have hw : |(2309607683/5000000000 : ℝ)|=(2309607683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3525519041/5000000000 : ℝ)|^17 ≤ (12664606191453/20000000000000 : ℝ)^13
        have hw : |(3525519041/5000000000 : ℝ)|=(3525519041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52033217/5000000000 : ℝ)|^17 ≤ (997728673/390625000000 : ℝ)^13
        have hw : |(-52033217/5000000000 : ℝ)|=(52033217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304051_s1_s1_12 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4605828509/10000000000 : ℝ)*x 0 + (7030603607/10000000000 : ℝ)*x 1 + (208380811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4605828509/10000000000 : ℝ)^17 ≤ (9070895445219/25000000000000 : ℝ)^13 := by
    have hnat : (4605828509 : ℕ)^17*25000000000000^13 ≤ 9070895445219^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4605828509 10000000000 9070895445219 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7030603607/10000000000 : ℝ)^17 ≤ (63083156568797/100000000000000 : ℝ)^13 := by
    have hnat : (7030603607 : ℕ)^17*100000000000000^13 ≤ 63083156568797^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7030603607 10000000000 63083156568797 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208380811/10000000000 : ℝ)^17 ≤ (9894713037/1562500000000 : ℝ)^13 := by
    have hnat : (208380811 : ℕ)^17*1562500000000^13 ≤ 9894713037^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208380811 10000000000 9894713037 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4605828509/10000000000 : ℝ), (7030603607/10000000000 : ℝ), (208380811/10000000000 : ℝ)] ![(9070895445219/25000000000000 : ℝ), (63083156568797/100000000000000 : ℝ), (9894713037/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4605828509/10000000000 : ℝ)|^17 ≤ (9070895445219/25000000000000 : ℝ)^13
        have hw : |(4605828509/10000000000 : ℝ)|=(4605828509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7030603607/10000000000 : ℝ)|^17 ≤ (63083156568797/100000000000000 : ℝ)^13
        have hw : |(7030603607/10000000000 : ℝ)|=(7030603607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208380811/10000000000 : ℝ)|^17 ≤ (9894713037/1562500000000 : ℝ)^13
        have hw : |(208380811/10000000000 : ℝ)|=(208380811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304051_s1_s1_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2751151559/10000000000 : ℝ)*x 0 + (620781439/2000000000 : ℝ)*x 1 + (3376640557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2751151559/10000000000 : ℝ)^17 ≤ (18495132374999/100000000000000 : ℝ)^13 := by
    have hnat : (2751151559 : ℕ)^17*100000000000000^13 ≤ 18495132374999^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751151559 10000000000 18495132374999 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620781439/2000000000 : ℝ)^17 ≤ (10827868077401/50000000000000 : ℝ)^13 := by
    have hnat : (620781439 : ℕ)^17*50000000000000^13 ≤ 10827868077401^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620781439 2000000000 10827868077401 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3376640557/5000000000 : ℝ)^17 ≤ (59849131456351/100000000000000 : ℝ)^13 := by
    have hnat : (3376640557 : ℕ)^17*100000000000000^13 ≤ 59849131456351^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3376640557 5000000000 59849131456351 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2751151559/10000000000 : ℝ), (620781439/2000000000 : ℝ), (3376640557/5000000000 : ℝ)] ![(18495132374999/100000000000000 : ℝ), (10827868077401/50000000000000 : ℝ), (59849131456351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2751151559/10000000000 : ℝ)|^17 ≤ (18495132374999/100000000000000 : ℝ)^13
        have hw : |(-2751151559/10000000000 : ℝ)|=(2751151559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(620781439/2000000000 : ℝ)|^17 ≤ (10827868077401/50000000000000 : ℝ)^13
        have hw : |(620781439/2000000000 : ℝ)|=(620781439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3376640557/5000000000 : ℝ)|^17 ≤ (59849131456351/100000000000000 : ℝ)^13
        have hw : |(3376640557/5000000000 : ℝ)|=(3376640557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304051_s1_s1_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1690048879/10000000000 : ℝ)*x 0 + (-95337439/500000000 : ℝ)*x 1 + (8331879113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1690048879/10000000000 : ℝ)^17 ≤ (4889898142877/50000000000000 : ℝ)^13 := by
    have hnat : (1690048879 : ℕ)^17*50000000000000^13 ≤ 4889898142877^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690048879 10000000000 4889898142877 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (95337439/500000000 : ℝ)^17 ≤ (5725525070367/50000000000000 : ℝ)^13 := by
    have hnat : (95337439 : ℕ)^17*50000000000000^13 ≤ 5725525070367^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95337439 500000000 5725525070367 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8331879113/10000000000 : ℝ)^17 ≤ (78769153564509/100000000000000 : ℝ)^13 := by
    have hnat : (8331879113 : ℕ)^17*100000000000000^13 ≤ 78769153564509^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8331879113 10000000000 78769153564509 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1690048879/10000000000 : ℝ), (-95337439/500000000 : ℝ), (8331879113/10000000000 : ℝ)] ![(4889898142877/50000000000000 : ℝ), (5725525070367/50000000000000 : ℝ), (78769153564509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1690048879/10000000000 : ℝ)|^17 ≤ (4889898142877/50000000000000 : ℝ)^13
        have hw : |(1690048879/10000000000 : ℝ)|=(1690048879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-95337439/500000000 : ℝ)|^17 ≤ (5725525070367/50000000000000 : ℝ)^13
        have hw : |(-95337439/500000000 : ℝ)|=(95337439/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8331879113/10000000000 : ℝ)|^17 ≤ (78769153564509/100000000000000 : ℝ)^13
        have hw : |(8331879113/10000000000 : ℝ)|=(8331879113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304051_s1_s1_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7034199059/10000000000 : ℝ)*x 0 + (4638375519/10000000000 : ℝ)*x 1 + (-104066411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7034199059/10000000000 : ℝ)^17 ≤ (3945334187911/6250000000000 : ℝ)^13 := by
    have hnat : (7034199059 : ℕ)^17*6250000000000^13 ≤ 3945334187911^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7034199059 10000000000 3945334187911 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4638375519/10000000000 : ℝ)^17 ≤ (18309617252321/50000000000000 : ℝ)^13 := by
    have hnat : (4638375519 : ℕ)^17*50000000000000^13 ≤ 18309617252321^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4638375519 10000000000 18309617252321 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104066411/10000000000 : ℝ)^17 ≤ (63854616617/25000000000000 : ℝ)^13 := by
    have hnat : (104066411 : ℕ)^17*25000000000000^13 ≤ 63854616617^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104066411 10000000000 63854616617 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7034199059/10000000000 : ℝ), (4638375519/10000000000 : ℝ), (-104066411/10000000000 : ℝ)] ![(3945334187911/6250000000000 : ℝ), (18309617252321/50000000000000 : ℝ), (63854616617/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7034199059/10000000000 : ℝ)|^17 ≤ (3945334187911/6250000000000 : ℝ)^13
        have hw : |(7034199059/10000000000 : ℝ)|=(7034199059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4638375519/10000000000 : ℝ)|^17 ≤ (18309617252321/50000000000000 : ℝ)^13
        have hw : |(4638375519/10000000000 : ℝ)|=(4638375519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104066411/10000000000 : ℝ)|^17 ≤ (63854616617/25000000000000 : ℝ)^13
        have hw : |(-104066411/10000000000 : ℝ)|=(104066411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304051_s1_s1_18 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3506904861/5000000000 : ℝ)*x 0 + (4624930719/10000000000 : ℝ)*x 1 + (104198937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3506904861/5000000000 : ℝ)^17 ≤ (7860772314969/12500000000000 : ℝ)^13 := by
    have hnat : (3506904861 : ℕ)^17*12500000000000^13 ≤ 7860772314969^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3506904861 5000000000 7860772314969 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4624930719/10000000000 : ℝ)^17 ≤ (36480492032279/100000000000000 : ℝ)^13 := by
    have hnat : (4624930719 : ℕ)^17*100000000000000^13 ≤ 36480492032279^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4624930719 10000000000 36480492032279 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104198937/5000000000 : ℝ)^17 ≤ (316664722039/50000000000000 : ℝ)^13 := by
    have hnat : (104198937 : ℕ)^17*50000000000000^13 ≤ 316664722039^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104198937 5000000000 316664722039 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3506904861/5000000000 : ℝ), (4624930719/10000000000 : ℝ), (104198937/5000000000 : ℝ)] ![(7860772314969/12500000000000 : ℝ), (36480492032279/100000000000000 : ℝ), (316664722039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3506904861/5000000000 : ℝ)|^17 ≤ (7860772314969/12500000000000 : ℝ)^13
        have hw : |(3506904861/5000000000 : ℝ)|=(3506904861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4624930719/10000000000 : ℝ)|^17 ≤ (36480492032279/100000000000000 : ℝ)^13
        have hw : |(4624930719/10000000000 : ℝ)|=(4624930719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104198937/5000000000 : ℝ)|^17 ≤ (316664722039/50000000000000 : ℝ)^13
        have hw : |(104198937/5000000000 : ℝ)|=(104198937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304051_s1_s1_19 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-952771759/2000000000 : ℝ)*x 0 + (2069780541/5000000000 : ℝ)*x 1 + (4035448073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (952771759/2000000000 : ℝ)^17 ≤ (7584017045753/20000000000000 : ℝ)^13 := by
    have hnat : (952771759 : ℕ)^17*20000000000000^13 ≤ 7584017045753^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952771759 2000000000 7584017045753 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069780541/5000000000 : ℝ)^17 ≤ (31556881459543/100000000000000 : ℝ)^13 := by
    have hnat : (2069780541 : ℕ)^17*100000000000000^13 ≤ 31556881459543^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069780541 5000000000 31556881459543 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035448073/10000000000 : ℝ)^17 ≤ (30523033298917/100000000000000 : ℝ)^13 := by
    have hnat : (4035448073 : ℕ)^17*100000000000000^13 ≤ 30523033298917^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035448073 10000000000 30523033298917 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-952771759/2000000000 : ℝ), (2069780541/5000000000 : ℝ), (4035448073/10000000000 : ℝ)] ![(7584017045753/20000000000000 : ℝ), (31556881459543/100000000000000 : ℝ), (30523033298917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-952771759/2000000000 : ℝ)|^17 ≤ (7584017045753/20000000000000 : ℝ)^13
        have hw : |(-952771759/2000000000 : ℝ)|=(952771759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2069780541/5000000000 : ℝ)|^17 ≤ (31556881459543/100000000000000 : ℝ)^13
        have hw : |(2069780541/5000000000 : ℝ)|=(2069780541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035448073/10000000000 : ℝ)|^17 ≤ (30523033298917/100000000000000 : ℝ)^13
        have hw : |(4035448073/10000000000 : ℝ)|=(4035448073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304051_s1_s1_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1673529491/10000000000 : ℝ)*x 0 + (-2270593833/10000000000 : ℝ)*x 1 + (4051683609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1673529491/10000000000 : ℝ)^17 ≤ (2413744729891/25000000000000 : ℝ)^13 := by
    have hnat : (1673529491 : ℕ)^17*25000000000000^13 ≤ 2413744729891^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1673529491 10000000000 2413744729891 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270593833/10000000000 : ℝ)^17 ≤ (14388930560039/100000000000000 : ℝ)^13 := by
    have hnat : (2270593833 : ℕ)^17*100000000000000^13 ≤ 14388930560039^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270593833 10000000000 14388930560039 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4051683609/5000000000 : ℝ)^17 ≤ (7595609050051/10000000000000 : ℝ)^13 := by
    have hnat : (4051683609 : ℕ)^17*10000000000000^13 ≤ 7595609050051^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4051683609 5000000000 7595609050051 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1673529491/10000000000 : ℝ), (-2270593833/10000000000 : ℝ), (4051683609/5000000000 : ℝ)] ![(2413744729891/25000000000000 : ℝ), (14388930560039/100000000000000 : ℝ), (7595609050051/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1673529491/10000000000 : ℝ)|^17 ≤ (2413744729891/25000000000000 : ℝ)^13
        have hw : |(1673529491/10000000000 : ℝ)|=(1673529491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2270593833/10000000000 : ℝ)|^17 ≤ (14388930560039/100000000000000 : ℝ)^13
        have hw : |(-2270593833/10000000000 : ℝ)|=(2270593833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4051683609/5000000000 : ℝ)|^17 ≤ (7595609050051/10000000000000 : ℝ)^13
        have hw : |(4051683609/5000000000 : ℝ)|=(4051683609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304051_s1_s1_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6748396481/10000000000 : ℝ)*x 0 + (2361568319/5000000000 : ℝ)*x 1 + (-25341333/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6748396481/10000000000 : ℝ)^17 ≤ (14948132350477/25000000000000 : ℝ)^13 := by
    have hnat : (6748396481 : ℕ)^17*25000000000000^13 ≤ 14948132350477^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6748396481 10000000000 14948132350477 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2361568319/5000000000 : ℝ)^17 ≤ (37496760031721/100000000000000 : ℝ)^13 := by
    have hnat : (2361568319 : ℕ)^17*100000000000000^13 ≤ 37496760031721^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2361568319 5000000000 37496760031721 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25341333/400000000 : ℝ)^17 ≤ (169419409313/6250000000000 : ℝ)^13 := by
    have hnat : (25341333 : ℕ)^17*6250000000000^13 ≤ 169419409313^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25341333 400000000 169419409313 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6748396481/10000000000 : ℝ), (2361568319/5000000000 : ℝ), (-25341333/400000000 : ℝ)] ![(14948132350477/25000000000000 : ℝ), (37496760031721/100000000000000 : ℝ), (169419409313/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6748396481/10000000000 : ℝ)|^17 ≤ (14948132350477/25000000000000 : ℝ)^13
        have hw : |(6748396481/10000000000 : ℝ)|=(6748396481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2361568319/5000000000 : ℝ)|^17 ≤ (37496760031721/100000000000000 : ℝ)^13
        have hw : |(2361568319/5000000000 : ℝ)|=(2361568319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25341333/400000000 : ℝ)|^17 ≤ (169419409313/6250000000000 : ℝ)^13
        have hw : |(-25341333/400000000 : ℝ)|=(25341333/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304051_s1_s1_25 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1562082893/5000000000 : ℝ)*x 0 + (8061926911/10000000000 : ℝ)*x 1 + (25341333/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1562082893/5000000000 : ℝ)^17 ≤ (21840754265423/100000000000000 : ℝ)^13 := by
    have hnat : (1562082893 : ℕ)^17*100000000000000^13 ≤ 21840754265423^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562082893 5000000000 21840754265423 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8061926911/10000000000 : ℝ)^17 ≤ (18862133793319/25000000000000 : ℝ)^13 := by
    have hnat : (8061926911 : ℕ)^17*25000000000000^13 ≤ 18862133793319^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8061926911 10000000000 18862133793319 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25341333/400000000 : ℝ)^17 ≤ (169419409313/6250000000000 : ℝ)^13 := by
    have hnat : (25341333 : ℕ)^17*6250000000000^13 ≤ 169419409313^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25341333 400000000 169419409313 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1562082893/5000000000 : ℝ), (8061926911/10000000000 : ℝ), (25341333/400000000 : ℝ)] ![(21840754265423/100000000000000 : ℝ), (18862133793319/25000000000000 : ℝ), (169419409313/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1562082893/5000000000 : ℝ)|^17 ≤ (21840754265423/100000000000000 : ℝ)^13
        have hw : |(1562082893/5000000000 : ℝ)|=(1562082893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8061926911/10000000000 : ℝ)|^17 ≤ (18862133793319/25000000000000 : ℝ)^13
        have hw : |(8061926911/10000000000 : ℝ)|=(8061926911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25341333/400000000 : ℝ)|^17 ≤ (169419409313/6250000000000 : ℝ)^13
        have hw : |(25341333/400000000 : ℝ)|=(25341333/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304051_s1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((5587/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5587/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17689/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17689/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(10271/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(10271/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((72527/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72527/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36187/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36187/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4369/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4369/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (5587/6250 : ℝ) ^ (33/8 : ℝ) ≤ (62966122190249021049/100000000000000000000 : ℝ) := by
    have hpowers : (5587/6250 : ℝ)^33 ≤ (62966122190249021049/100000000000000000000 : ℝ)^8 := by
      have hnat : (5587 : ℕ)^33*100000000000000000000^8 ≤ 62966122190249021049^8*6250^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5587 6250 62966122190249021049 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5587/6250 : ℝ)) (X := (62966122190249021049/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (162966122190249021049/100000000000000000000 : ℝ) ≤ (11256866999894631/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (162966122190249021049/100000000000000000000 : ℝ)^8 ≤ (11256866999894631/10000000000000000 : ℝ)^33 := by
      have hnat : (162966122190249021049 : ℕ)^8*10000000000000000^33 ≤ 11256866999894631^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        162966122190249021049 100000000000000000000 11256866999894631 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11256866999894631/10000000000000000 : ℝ)) (X := (162966122190249021049/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (112966122190249021049/50000000000000000000 : ℝ) ≤ (3046161393530647/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (112966122190249021049/50000000000000000000 : ℝ)^8 ≤ (3046161393530647/2500000000000000 : ℝ)^33 := by
      have hnat : (112966122190249021049 : ℕ)^8*2500000000000000^33 ≤ 3046161393530647^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112966122190249021049 50000000000000000000 3046161393530647 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3046161393530647/2500000000000000 : ℝ)) (X := (112966122190249021049/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1256866999894631/8939200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(927778574227957/8939200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (5587/6250 : ℝ)) (alpha := (1256866999894631/8939200000000000 : ℝ)) (beta := (927778574227957/8939200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5587/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1256866999894631/8939200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(927778574227957/8939200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (17689/20000 : ℝ) ^ (33/8 : ℝ) ≤ (3766234204018600073/6250000000000000000 : ℝ) := by
    have hpowers : (17689/20000 : ℝ)^33 ≤ (3766234204018600073/6250000000000000000 : ℝ)^8 := by
      have hnat : (17689 : ℕ)^33*6250000000000000000^8 ≤ 3766234204018600073^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17689 20000 3766234204018600073 6250000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17689/20000 : ℝ)) (X := (3766234204018600073/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (10016234204018600073/6250000000000000000 : ℝ) ≤ (5605629852528719/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (10016234204018600073/6250000000000000000 : ℝ)^8 ≤ (5605629852528719/5000000000000000 : ℝ)^33 := by
      have hnat : (10016234204018600073 : ℕ)^8*5000000000000000^33 ≤ 5605629852528719^33*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10016234204018600073 6250000000000000000 5605629852528719 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5605629852528719/5000000000000000 : ℝ)) (X := (10016234204018600073/6250000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (6891234204018600073/3125000000000000000 : ℝ) ≤ (12113227559183663/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (6891234204018600073/3125000000000000000 : ℝ)^8 ≤ (12113227559183663/10000000000000000 : ℝ)^33 := by
      have hnat : (6891234204018600073 : ℕ)^8*10000000000000000^33 ≤ 12113227559183663^33*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6891234204018600073 3125000000000000000 12113227559183663 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12113227559183663/10000000000000000 : ℝ)) (X := (6891234204018600073/3125000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(605629852528719/4422250000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(36078714165049/353780000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (17689/20000 : ℝ)) (alpha := (605629852528719/4422250000000000 : ℝ)) (beta := (36078714165049/353780000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (17689/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(605629852528719/4422250000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(36078714165049/353780000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (10271/20000 : ℝ) ^ (33/8 : ℝ) ≤ (3199806971325735697/50000000000000000000 : ℝ) := by
    have hpowers : (10271/20000 : ℝ)^33 ≤ (3199806971325735697/50000000000000000000 : ℝ)^8 := by
      have hnat : (10271 : ℕ)^33*50000000000000000000^8 ≤ 3199806971325735697^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10271 20000 3199806971325735697 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10271/20000 : ℝ)) (X := (3199806971325735697/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (53199806971325735697/50000000000000000000 : ℝ) ≤ (634469776709177/625000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (53199806971325735697/50000000000000000000 : ℝ)^8 ≤ (634469776709177/625000000000000 : ℝ)^33 := by
      have hnat : (53199806971325735697 : ℕ)^8*625000000000000^33 ≤ 634469776709177^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53199806971325735697 50000000000000000000 634469776709177 625000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (634469776709177/625000000000000 : ℝ)) (X := (53199806971325735697/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (28199806971325735697/25000000000000000000 : ℝ) ≤ (5148139156005329/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (28199806971325735697/25000000000000000000 : ℝ)^8 ≤ (5148139156005329/5000000000000000 : ℝ)^33 := by
      have hnat : (28199806971325735697 : ℕ)^8*5000000000000000^33 ≤ 5148139156005329^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28199806971325735697 25000000000000000000 5148139156005329 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5148139156005329/5000000000000000 : ℝ)) (X := (28199806971325735697/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(9469776709177/320968750000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(72380942331913/2567750000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (10271/20000 : ℝ)) (alpha := (9469776709177/320968750000000 : ℝ)) (beta := (72380942331913/2567750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (10271/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(9469776709177/320968750000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(72380942331913/2567750000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3660542971/10000000000 : ℝ)*X 0 0+(1822528519/5000000000 : ℝ)*X 0 1+(5559804809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304051_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2619449663/10000000000 : ℝ)*X 1 0+(-2608368077/10000000000 : ℝ)*X 1 1+(3613779577/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304051_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2832463269/5000000000 : ℝ)*X 2 0+(2841559749/5000000000 : ℝ)*X 2 1+(-240375727/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304051_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-62397553/200000000 : ℝ)*X 0 0+(2734946993/10000000000 : ℝ)*X 0 1+(6752979447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304051_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1916724611/10000000000 : ℝ)*X 1 0+(-840119517/5000000000 : ℝ)*X 1 1+(2082884031/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304051_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2309607683/5000000000 : ℝ)*X 2 0+(3525519041/5000000000 : ℝ)*X 2 1+(-52033217/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304051_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((4605828509/10000000000 : ℝ)*X 0 0+(7030603607/10000000000 : ℝ)*X 0 1+(208380811/10000000000 : ℝ)*X 0 2+(4605828509/10000000000 : ℝ)*X 1 0+(7030603607/10000000000 : ℝ)*X 1 1+(208380811/10000000000 : ℝ)*X 1 2+(4605828509/10000000000 : ℝ)*X 2 0+(7030603607/10000000000 : ℝ)*X 2 1+(208380811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304051_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-2751151559/10000000000 : ℝ)*X 0 0+(620781439/2000000000 : ℝ)*X 0 1+(3376640557/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304051_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((1690048879/10000000000 : ℝ)*X 1 0+(-95337439/500000000 : ℝ)*X 1 1+(8331879113/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304051_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((7034199059/10000000000 : ℝ)*X 2 0+(4638375519/10000000000 : ℝ)*X 2 1+(-104066411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304051_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((3506904861/5000000000 : ℝ)*X 0 0+(4624930719/10000000000 : ℝ)*X 0 1+(104198937/5000000000 : ℝ)*X 0 2+(3506904861/5000000000 : ℝ)*X 1 0+(4624930719/10000000000 : ℝ)*X 1 1+(104198937/5000000000 : ℝ)*X 1 2+(3506904861/5000000000 : ℝ)*X 2 0+(4624930719/10000000000 : ℝ)*X 2 1+(104198937/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304051_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-952771759/2000000000 : ℝ)*X 0 0+(2069780541/5000000000 : ℝ)*X 0 1+(4035448073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304051_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1673529491/10000000000 : ℝ)*X 1 0+(-2270593833/10000000000 : ℝ)*X 1 1+(4051683609/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304051_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((6748396481/10000000000 : ℝ)*X 2 0+(2361568319/5000000000 : ℝ)*X 2 1+(-25341333/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304051_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((1562082893/5000000000 : ℝ)*X 0 0+(8061926911/10000000000 : ℝ)*X 0 1+(25341333/400000000 : ℝ)*X 0 2+(1562082893/5000000000 : ℝ)*X 1 0+(8061926911/10000000000 : ℝ)*X 1 1+(25341333/400000000 : ℝ)*X 1 2+(1562082893/5000000000 : ℝ)*X 2 0+(8061926911/10000000000 : ℝ)*X 2 1+(25341333/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304051_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((72527/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72527/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (39389269246666098340943580491769/4060267752212000000000000000000000000 : ℝ) := by norm_num
    linear_combination (95288510837/500000000000 : ℝ)*(base7) + (971007143/500000000000 : ℝ)*(base49) + (30810449231/500000000000 : ℝ)*(base59) + (661484353699/1000000000000 : ℝ)*(base60) + (3541896751431/1000000000000 : ℝ)*(major_s1_0) + (3541896751431/1000000000000 : ℝ)*(major_s1_1) + (3541896751431/1000000000000 : ℝ)*(major_s1_2) + (1633431/500000000000 : ℝ)*(sp_s1_0) + (4629162465237/1000000000000 : ℝ)*(sp_s1_7) + (925845877497/200000000000 : ℝ)*(sp_s1_8) + (1157310322977/250000000000 : ℝ)*(sp_s1_9) + (1262905721473/500000000000 : ℝ)*(sp_s1_12) + (590311/7812500000 : ℝ)*(sp_s1_13) + (11904423/1000000000000 : ℝ)*(sp_s1_20) + (291904302659/125000000000 : ℝ)*(f.failure) + (1157310322977/250000000000 : ℝ)*(f.sum) + (171195085921280051/1816837190000000000000000000000 : ℝ)*base62 + (648100916131361/1283875000000000000000000000 : ℝ)*base64 + (220306303063411/353780000000000000000000000 : ℝ)*base67 + (178630249527673/1283875000000000000000000000 : ℝ)*base68 + (206897671448172538293/459072616000000000000000000000000 : ℝ)*base70 + (4443842318878733/8939200000000000000000000000 : ℝ)*base72 + (2580379181631561/4422250000000000000000000000 : ℝ)*base74 + (6931804631930799/8939200000000000000000000000 : ℝ)*base76 + (52427370375675498603/158125508800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (2087/3125000000000000 : ℝ)*base87 + (2087/3125000000000000 : ℝ)*base89 + (2087/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36187/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36187/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2910219701769827436974296815231/507533469026500000000000000000000000 : ℝ) := by norm_num
    linear_combination (95358901881/500000000000 : ℝ)*(base7) + (120427841/62500000000 : ℝ)*(base49) + (57056463549/100000000000 : ℝ)*(base59) + (882413468181/1000000000000 : ℝ)*(base60) + (442303020169/125000000000 : ℝ)*(major_s1_0) + (442303020169/125000000000 : ℝ)*(major_s1_1) + (442303020169/125000000000 : ℝ)*(major_s1_2) + (284273/250000000000 : ℝ)*(sp_s1_0) + (92106661/1000000000000 : ℝ)*(sp_s1_8) + (2312248848453/500000000000 : ℝ)*(sp_s1_13) + (4624397102347/1000000000000 : ℝ)*(sp_s1_14) + (2312249416999/500000000000 : ℝ)*(sp_s1_15) + (2523662685713/1000000000000 : ℝ)*(sp_s1_18) + (962499/100000000000 : ℝ)*(sp_s1_20) + (2332944881951/1000000000000 : ℝ)*(f.failure) + (2312249416999/500000000000 : ℝ)*(f.sum) + (37412670359613217/113552324375000000000000000000 : ℝ)*base62 + (2969693523906699/2567750000000000000000000000 : ℝ)*base64 + (4258004625131/17689000000000000000000000 : ℝ)*base66 + (211813470314679/320968750000000000000000000 : ℝ)*base68 + (47004427866664364407/57384077000000000000000000000000 : ℝ)*base70 + (587624413358447/1117400000000000000000000000 : ℝ)*base72 + (493142578265803/1105562500000000000000000000 : ℝ)*base74 + (387495049117021/1117400000000000000000000000 : ℝ)*base76 + (3519476822893508037/19765688600000000000000000000000 : ℝ)*base79 + (9009/12500000000000000 : ℝ)*base87 + (9009/12500000000000000 : ℝ)*base89 + (9009/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4369/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4369/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1395522040575999635057333633697/507533469026500000000000000000000000 : ℝ) := by norm_num
    linear_combination (12857336671/100000000000 : ℝ)*(base5) + (3963081161/15625000000 : ℝ)*(base39) + (27313/62500000000 : ℝ)*(base44) + (6996861141/20000000000 : ℝ)*(base49) + (888490733397/500000000000 : ℝ)*(major_s1_0) + (888490514893/500000000000 : ℝ)*(major_s1_1) + (888490733397/500000000000 : ℝ)*(major_s1_2) + (7410309/1000000000000 : ℝ)*(sp_s1_1) + (3581087/500000000000 : ℝ)*(sp_s1_2) + (28393657/500000000000 : ℝ)*(sp_s1_15) + (2382367084033/1000000000000 : ℝ)*(sp_s1_19) + (476471847343/200000000000 : ℝ)*(sp_s1_20) + (502175300251/200000000000 : ℝ)*(sp_s1_21) + (1043021129291/1000000000000 : ℝ)*(sp_s1_25) + (1171594933009/1000000000000 : ℝ)*(f.failure) + (2382367084033/1000000000000 : ℝ)*(f.sum) + (8508873649339605133/45420929750000000000000000000000 : ℝ)*base63 + (1384450079704497/2567750000000000000000000000 : ℝ)*base65 + (77087371459267/176890000000000000000000000 : ℝ)*base67 + (317737681684373/1283875000000000000000000000 : ℝ)*base69 + (26729783873608433009/229536308000000000000000000000000 : ℝ)*base71 + (3278880109124169/4469600000000000000000000000 : ℝ)*base73 + (464728296290641/4422250000000000000000000000 : ℝ)*base74 + (2064228037484867/4469600000000000000000000000 : ℝ)*base77 + (49719317734891157601/79062754400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (7369/12500000000000000 : ℝ)*base86 + (7369/12500000000000000 : ℝ)*base88 + (7369/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((5587/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5587/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17689/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17689/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(10271/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(10271/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((72527/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(72527/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36187/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36187/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4369/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4369/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304051_s1 p hpa hpb X hX hprev0

#print axioms solution

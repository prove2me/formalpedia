-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302059_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:22:59.232541+00:00
-- url     : https://prove2.me/submissions/1ff5412e-0afd-44a9-bd68-a49007880074

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
theorem collision_support_c302059_s4_s4_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6013888471/10000000000 : ℝ)*x 0 + (5577647341/10000000000 : ℝ)*x 1 + (-334580357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6013888471/10000000000 : ℝ)^131 ≤ (12755904393299/25000000000000 : ℝ)^99 := by
    have hnat : (6013888471 : ℕ)^131*25000000000000^99 ≤ 12755904393299^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6013888471 10000000000 12755904393299 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5577647341/10000000000 : ℝ)^131 ≤ (23092228182181/50000000000000 : ℝ)^99 := by
    have hnat : (5577647341 : ℕ)^131*50000000000000^99 ≤ 23092228182181^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5577647341 10000000000 23092228182181 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (334580357/5000000000 : ℝ)^131 ≤ (558385208979/20000000000000 : ℝ)^99 := by
    have hnat : (334580357 : ℕ)^131*20000000000000^99 ≤ 558385208979^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334580357 5000000000 558385208979 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6013888471/10000000000 : ℝ), (5577647341/10000000000 : ℝ), (-334580357/5000000000 : ℝ)] ![(12755904393299/25000000000000 : ℝ), (23092228182181/50000000000000 : ℝ), (558385208979/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6013888471/10000000000 : ℝ)|^131 ≤ (12755904393299/25000000000000 : ℝ)^99
        have hw : |(6013888471/10000000000 : ℝ)|=(6013888471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5577647341/10000000000 : ℝ)|^131 ≤ (23092228182181/50000000000000 : ℝ)^99
        have hw : |(5577647341/10000000000 : ℝ)|=(5577647341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-334580357/5000000000 : ℝ)|^131 ≤ (558385208979/20000000000000 : ℝ)^99
        have hw : |(-334580357/5000000000 : ℝ)|=(334580357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s4_s4_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4199983631/10000000000 : ℝ)*x 0 + (5153301069/10000000000 : ℝ)*x 1 + (920991963/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4199983631/10000000000 : ℝ)^131 ≤ (31729924851811/100000000000000 : ℝ)^99 := by
    have hnat : (4199983631 : ℕ)^131*100000000000000^99 ≤ 31729924851811^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199983631 10000000000 31729924851811 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5153301069/10000000000 : ℝ)^131 ≤ (41593191743731/100000000000000 : ℝ)^99 := by
    have hnat : (5153301069 : ℕ)^131*100000000000000^99 ≤ 41593191743731^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153301069 10000000000 41593191743731 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (920991963/2500000000 : ℝ)^131 ≤ (3334610423847/12500000000000 : ℝ)^99 := by
    have hnat : (920991963 : ℕ)^131*12500000000000^99 ≤ 3334610423847^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920991963 2500000000 3334610423847 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4199983631/10000000000 : ℝ), (5153301069/10000000000 : ℝ), (920991963/2500000000 : ℝ)] ![(31729924851811/100000000000000 : ℝ), (41593191743731/100000000000000 : ℝ), (3334610423847/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4199983631/10000000000 : ℝ)|^131 ≤ (31729924851811/100000000000000 : ℝ)^99
        have hw : |(4199983631/10000000000 : ℝ)|=(4199983631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5153301069/10000000000 : ℝ)|^131 ≤ (41593191743731/100000000000000 : ℝ)^99
        have hw : |(5153301069/10000000000 : ℝ)|=(5153301069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(920991963/2500000000 : ℝ)|^131 ≤ (3334610423847/12500000000000 : ℝ)^99
        have hw : |(920991963/2500000000 : ℝ)|=(920991963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s4_s4_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3028284013/10000000000 : ℝ)*x 0 + (21470771/78125000 : ℝ)*x 1 + (6909660833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3028284013/10000000000 : ℝ)^131 ≤ (4116542205409/20000000000000 : ℝ)^99 := by
    have hnat : (3028284013 : ℕ)^131*20000000000000^99 ≤ 4116542205409^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3028284013 10000000000 4116542205409 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21470771/78125000 : ℝ)^131 ≤ (18102680959689/100000000000000 : ℝ)^99 := by
    have hnat : (21470771 : ℕ)^131*100000000000000^99 ≤ 18102680959689^99*78125000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21470771 78125000 18102680959689 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6909660833/10000000000 : ℝ)^131 ≤ (1532865200051/2500000000000 : ℝ)^99 := by
    have hnat : (6909660833 : ℕ)^131*2500000000000^99 ≤ 1532865200051^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6909660833 10000000000 1532865200051 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3028284013/10000000000 : ℝ), (21470771/78125000 : ℝ), (6909660833/10000000000 : ℝ)] ![(4116542205409/20000000000000 : ℝ), (18102680959689/100000000000000 : ℝ), (1532865200051/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3028284013/10000000000 : ℝ)|^131 ≤ (4116542205409/20000000000000 : ℝ)^99
        have hw : |(-3028284013/10000000000 : ℝ)|=(3028284013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21470771/78125000 : ℝ)|^131 ≤ (18102680959689/100000000000000 : ℝ)^99
        have hw : |(21470771/78125000 : ℝ)|=(21470771/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6909660833/10000000000 : ℝ)|^131 ≤ (1532865200051/2500000000000 : ℝ)^99
        have hw : |(6909660833/10000000000 : ℝ)|=(6909660833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s4_s4_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (121898463/400000000 : ℝ)*x 0 + (-2694811553/10000000000 : ℝ)*x 1 + (6934490847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121898463/400000000 : ℝ)^131 ≤ (20755366004647/100000000000000 : ℝ)^99 := by
    have hnat : (121898463 : ℕ)^131*100000000000000^99 ≤ 20755366004647^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121898463 400000000 20755366004647 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694811553/10000000000 : ℝ)^131 ≤ (17638301927377/100000000000000 : ℝ)^99 := by
    have hnat : (2694811553 : ℕ)^131*100000000000000^99 ≤ 17638301927377^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694811553 10000000000 17638301927377 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6934490847/10000000000 : ℝ)^131 ≤ (308031660279/500000000000 : ℝ)^99 := by
    have hnat : (6934490847 : ℕ)^131*500000000000^99 ≤ 308031660279^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6934490847 10000000000 308031660279 500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(121898463/400000000 : ℝ), (-2694811553/10000000000 : ℝ), (6934490847/10000000000 : ℝ)] ![(20755366004647/100000000000000 : ℝ), (17638301927377/100000000000000 : ℝ), (308031660279/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(121898463/400000000 : ℝ)|^131 ≤ (20755366004647/100000000000000 : ℝ)^99
        have hw : |(121898463/400000000 : ℝ)|=(121898463/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2694811553/10000000000 : ℝ)|^131 ≤ (17638301927377/100000000000000 : ℝ)^99
        have hw : |(-2694811553/10000000000 : ℝ)|=(2694811553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6934490847/10000000000 : ℝ)|^131 ≤ (308031660279/500000000000 : ℝ)^99
        have hw : |(6934490847/10000000000 : ℝ)|=(6934490847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s4_s4_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2807232437/5000000000 : ℝ)*x 0 + (778069721/1250000000 : ℝ)*x 1 + (-9263681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2807232437/5000000000 : ℝ)^131 ≤ (46588285776771/100000000000000 : ℝ)^99 := by
    have hnat : (2807232437 : ℕ)^131*100000000000000^99 ≤ 46588285776771^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2807232437 5000000000 46588285776771 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (778069721/1250000000 : ℝ)^131 ≤ (53402023622693/100000000000000 : ℝ)^99 := by
    have hnat : (778069721 : ℕ)^131*100000000000000^99 ≤ 53402023622693^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778069721 1250000000 53402023622693 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9263681/10000000000 : ℝ)^131 ≤ (1938117043/20000000000000 : ℝ)^99 := by
    have hnat : (9263681 : ℕ)^131*20000000000000^99 ≤ 1938117043^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9263681 10000000000 1938117043 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2807232437/5000000000 : ℝ), (778069721/1250000000 : ℝ), (-9263681/10000000000 : ℝ)] ![(46588285776771/100000000000000 : ℝ), (53402023622693/100000000000000 : ℝ), (1938117043/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2807232437/5000000000 : ℝ)|^131 ≤ (46588285776771/100000000000000 : ℝ)^99
        have hw : |(2807232437/5000000000 : ℝ)|=(2807232437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(778069721/1250000000 : ℝ)|^131 ≤ (53402023622693/100000000000000 : ℝ)^99
        have hw : |(778069721/1250000000 : ℝ)|=(778069721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9263681/10000000000 : ℝ)|^131 ≤ (1938117043/20000000000000 : ℝ)^99
        have hw : |(-9263681/10000000000 : ℝ)|=(9263681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s4_s4_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3660099349/10000000000 : ℝ)*x 0 + (6692422761/10000000000 : ℝ)*x 1 + (589284761/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3660099349/10000000000 : ℝ)^131 ≤ (3306051956731/12500000000000 : ℝ)^99 := by
    have hnat : (3660099349 : ℕ)^131*12500000000000^99 ≤ 3306051956731^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3660099349 10000000000 3306051956731 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6692422761/10000000000 : ℝ)^131 ≤ (2938842275703/5000000000000 : ℝ)^99 := by
    have hnat : (6692422761 : ℕ)^131*5000000000000^99 ≤ 2938842275703^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6692422761 10000000000 2938842275703 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (589284761/2500000000 : ℝ)^131 ≤ (2954947763187/20000000000000 : ℝ)^99 := by
    have hnat : (589284761 : ℕ)^131*20000000000000^99 ≤ 2954947763187^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589284761 2500000000 2954947763187 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3660099349/10000000000 : ℝ), (6692422761/10000000000 : ℝ), (589284761/2500000000 : ℝ)] ![(3306051956731/12500000000000 : ℝ), (2938842275703/5000000000000 : ℝ), (2954947763187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3660099349/10000000000 : ℝ)|^131 ≤ (3306051956731/12500000000000 : ℝ)^99
        have hw : |(3660099349/10000000000 : ℝ)|=(3660099349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6692422761/10000000000 : ℝ)|^131 ≤ (2938842275703/5000000000000 : ℝ)^99
        have hw : |(6692422761/10000000000 : ℝ)|=(6692422761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(589284761/2500000000 : ℝ)|^131 ≤ (2954947763187/20000000000000 : ℝ)^99
        have hw : |(589284761/2500000000 : ℝ)|=(589284761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s4_s4_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-548404211/2000000000 : ℝ)*x 0 + (759065761/2500000000 : ℝ)*x 1 + (3454087573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548404211/2000000000 : ℝ)^131 ≤ (9024166590937/50000000000000 : ℝ)^99 := by
    have hnat : (548404211 : ℕ)^131*50000000000000^99 ≤ 9024166590937^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548404211 2000000000 9024166590937 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (759065761/2500000000 : ℝ)^131 ≤ (5163625796501/25000000000000 : ℝ)^99 := by
    have hnat : (759065761 : ℕ)^131*25000000000000^99 ≤ 5163625796501^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759065761 2500000000 5163625796501 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3454087573/5000000000 : ℝ)^131 ≤ (30648581810641/50000000000000 : ℝ)^99 := by
    have hnat : (3454087573 : ℕ)^131*50000000000000^99 ≤ 30648581810641^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3454087573 5000000000 30648581810641 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548404211/2000000000 : ℝ), (759065761/2500000000 : ℝ), (3454087573/5000000000 : ℝ)] ![(9024166590937/50000000000000 : ℝ), (5163625796501/25000000000000 : ℝ), (30648581810641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548404211/2000000000 : ℝ)|^131 ≤ (9024166590937/50000000000000 : ℝ)^99
        have hw : |(-548404211/2000000000 : ℝ)|=(548404211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(759065761/2500000000 : ℝ)|^131 ≤ (5163625796501/25000000000000 : ℝ)^99
        have hw : |(759065761/2500000000 : ℝ)|=(759065761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3454087573/5000000000 : ℝ)|^131 ≤ (30648581810641/50000000000000 : ℝ)^99
        have hw : |(3454087573/5000000000 : ℝ)|=(3454087573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s4_s4_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2723749991/10000000000 : ℝ)*x 0 + (-604301129/2000000000 : ℝ)*x 1 + (6933004563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2723749991/10000000000 : ℝ)^131 ≤ (17889369613849/100000000000000 : ℝ)^99 := by
    have hnat : (2723749991 : ℕ)^131*100000000000000^99 ≤ 17889369613849^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723749991 10000000000 17889369613849 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (604301129/2000000000 : ℝ)^131 ≤ (641305311481/3125000000000 : ℝ)^99 := by
    have hnat : (604301129 : ℕ)^131*3125000000000^99 ≤ 641305311481^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604301129 2000000000 641305311481 3125000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6933004563/10000000000 : ℝ)^131 ≤ (7698607552179/12500000000000 : ℝ)^99 := by
    have hnat : (6933004563 : ℕ)^131*12500000000000^99 ≤ 7698607552179^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6933004563 10000000000 7698607552179 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2723749991/10000000000 : ℝ), (-604301129/2000000000 : ℝ), (6933004563/10000000000 : ℝ)] ![(17889369613849/100000000000000 : ℝ), (641305311481/3125000000000 : ℝ), (7698607552179/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2723749991/10000000000 : ℝ)|^131 ≤ (17889369613849/100000000000000 : ℝ)^99
        have hw : |(2723749991/10000000000 : ℝ)|=(2723749991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-604301129/2000000000 : ℝ)|^131 ≤ (641305311481/3125000000000 : ℝ)^99
        have hw : |(-604301129/2000000000 : ℝ)|=(604301129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6933004563/10000000000 : ℝ)|^131 ≤ (7698607552179/12500000000000 : ℝ)^99
        have hw : |(6933004563/10000000000 : ℝ)|=(6933004563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s4_s4_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6651090339/10000000000 : ℝ)*x 0 + (5162476901/10000000000 : ℝ)*x 1 + (-10748557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6651090339/10000000000 : ℝ)^131 ≤ (29148492203023/50000000000000 : ℝ)^99 := by
    have hnat : (6651090339 : ℕ)^131*50000000000000^99 ≤ 29148492203023^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6651090339 10000000000 29148492203023 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5162476901/10000000000 : ℝ)^131 ≤ (5211402271971/12500000000000 : ℝ)^99 := by
    have hnat : (5162476901 : ℕ)^131*12500000000000^99 ≤ 5211402271971^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5162476901 10000000000 5211402271971 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10748557/10000000000 : ℝ)^131 ≤ (11797407491/100000000000000 : ℝ)^99 := by
    have hnat : (10748557 : ℕ)^131*100000000000000^99 ≤ 11797407491^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10748557 10000000000 11797407491 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6651090339/10000000000 : ℝ), (5162476901/10000000000 : ℝ), (-10748557/10000000000 : ℝ)] ![(29148492203023/50000000000000 : ℝ), (5211402271971/12500000000000 : ℝ), (11797407491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6651090339/10000000000 : ℝ)|^131 ≤ (29148492203023/50000000000000 : ℝ)^99
        have hw : |(6651090339/10000000000 : ℝ)|=(6651090339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5162476901/10000000000 : ℝ)|^131 ≤ (5211402271971/12500000000000 : ℝ)^99
        have hw : |(5162476901/10000000000 : ℝ)|=(5162476901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10748557/10000000000 : ℝ)|^131 ≤ (11797407491/100000000000000 : ℝ)^99
        have hw : |(-10748557/10000000000 : ℝ)|=(10748557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s4_s4_19 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-457/2500000000 : ℝ)*x 0 + (457/2500000000 : ℝ)*x 1 + (9999999981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (457/2500000000 : ℝ)^131 ≤ (30337/25000000000000 : ℝ)^99 := by
    have hnat : (457 : ℕ)^131*25000000000000^99 ≤ 30337^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457 2500000000 30337 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (457/2500000000 : ℝ)^131 ≤ (30337/25000000000000 : ℝ)^99 := by
    have hnat : (457 : ℕ)^131*25000000000000^99 ≤ 30337^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457 2500000000 30337 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9999999981/10000000000 : ℝ)^131 ≤ (49999999874293/50000000000000 : ℝ)^99 := by
    have hnat : (9999999981 : ℕ)^131*50000000000000^99 ≤ 49999999874293^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999981 10000000000 49999999874293 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-457/2500000000 : ℝ), (457/2500000000 : ℝ), (9999999981/10000000000 : ℝ)] ![(30337/25000000000000 : ℝ), (30337/25000000000000 : ℝ), (49999999874293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-457/2500000000 : ℝ)|^131 ≤ (30337/25000000000000 : ℝ)^99
        have hw : |(-457/2500000000 : ℝ)|=(457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(457/2500000000 : ℝ)|^131 ≤ (30337/25000000000000 : ℝ)^99
        have hw : |(457/2500000000 : ℝ)|=(457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9999999981/10000000000 : ℝ)|^131 ≤ (49999999874293/50000000000000 : ℝ)^99
        have hw : |(9999999981/10000000000 : ℝ)|=(9999999981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s4_s4_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5801414333/10000000000 : ℝ)*x 0 + (4673612429/10000000000 : ℝ)*x 1 + (118004263/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5801414333/10000000000 : ℝ)^131 ≤ (48651965646619/100000000000000 : ℝ)^99 := by
    have hnat : (5801414333 : ℕ)^131*100000000000000^99 ≤ 48651965646619^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5801414333 10000000000 48651965646619 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4673612429/10000000000 : ℝ)^131 ≤ (18274427147957/50000000000000 : ℝ)^99 := by
    have hnat : (4673612429 : ℕ)^131*50000000000000^99 ≤ 18274427147957^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4673612429 10000000000 18274427147957 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118004263/500000000 : ℝ)^131 ≤ (739959002111/5000000000000 : ℝ)^99 := by
    have hnat : (118004263 : ℕ)^131*5000000000000^99 ≤ 739959002111^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118004263 500000000 739959002111 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5801414333/10000000000 : ℝ), (4673612429/10000000000 : ℝ), (118004263/500000000 : ℝ)] ![(48651965646619/100000000000000 : ℝ), (18274427147957/50000000000000 : ℝ), (739959002111/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5801414333/10000000000 : ℝ)|^131 ≤ (48651965646619/100000000000000 : ℝ)^99
        have hw : |(5801414333/10000000000 : ℝ)|=(5801414333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4673612429/10000000000 : ℝ)|^131 ≤ (18274427147957/50000000000000 : ℝ)^99
        have hw : |(4673612429/10000000000 : ℝ)|=(4673612429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(118004263/500000000 : ℝ)|^131 ≤ (739959002111/5000000000000 : ℝ)^99
        have hw : |(118004263/500000000 : ℝ)|=(118004263/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s4_s4_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1704959659/5000000000 : ℝ)*x 0 + (3422523759/10000000000 : ℝ)*x 1 + (6075458739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1704959659/5000000000 : ℝ)^131 ≤ (12041536282363/50000000000000 : ℝ)^99 := by
    have hnat : (1704959659 : ℕ)^131*50000000000000^99 ≤ 12041536282363^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704959659 5000000000 12041536282363 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3422523759/10000000000 : ℝ)^131 ≤ (24200938046401/100000000000000 : ℝ)^99 := by
    have hnat : (3422523759 : ℕ)^131*100000000000000^99 ≤ 24200938046401^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3422523759 10000000000 24200938046401 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6075458739/10000000000 : ℝ)^131 ≤ (404031167021/781250000000 : ℝ)^99 := by
    have hnat : (6075458739 : ℕ)^131*781250000000^99 ≤ 404031167021^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6075458739 10000000000 404031167021 781250000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1704959659/5000000000 : ℝ), (3422523759/10000000000 : ℝ), (6075458739/10000000000 : ℝ)] ![(12041536282363/50000000000000 : ℝ), (24200938046401/100000000000000 : ℝ), (404031167021/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1704959659/5000000000 : ℝ)|^131 ≤ (12041536282363/50000000000000 : ℝ)^99
        have hw : |(-1704959659/5000000000 : ℝ)|=(1704959659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3422523759/10000000000 : ℝ)|^131 ≤ (24200938046401/100000000000000 : ℝ)^99
        have hw : |(3422523759/10000000000 : ℝ)|=(3422523759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6075458739/10000000000 : ℝ)|^131 ≤ (404031167021/781250000000 : ℝ)^99
        have hw : |(6075458739/10000000000 : ℝ)|=(6075458739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s4_s4_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3345360897/10000000000 : ℝ)*x 0 + (-336786389/1000000000 : ℝ)*x 1 + (6173889467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3345360897/10000000000 : ℝ)^131 ≤ (939263759709/4000000000000 : ℝ)^99 := by
    have hnat : (3345360897 : ℕ)^131*4000000000000^99 ≤ 939263759709^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3345360897 10000000000 939263759709 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336786389/1000000000 : ℝ)^131 ≤ (11845413970337/50000000000000 : ℝ)^99 := by
    have hnat : (336786389 : ℕ)^131*50000000000000^99 ≤ 11845413970337^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336786389 1000000000 11845413970337 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6173889467/10000000000 : ℝ)^131 ≤ (211310312223/400000000000 : ℝ)^99 := by
    have hnat : (6173889467 : ℕ)^131*400000000000^99 ≤ 211310312223^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6173889467 10000000000 211310312223 400000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3345360897/10000000000 : ℝ), (-336786389/1000000000 : ℝ), (6173889467/10000000000 : ℝ)] ![(939263759709/4000000000000 : ℝ), (11845413970337/50000000000000 : ℝ), (211310312223/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3345360897/10000000000 : ℝ)|^131 ≤ (939263759709/4000000000000 : ℝ)^99
        have hw : |(3345360897/10000000000 : ℝ)|=(3345360897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-336786389/1000000000 : ℝ)|^131 ≤ (11845413970337/50000000000000 : ℝ)^99
        have hw : |(-336786389/1000000000 : ℝ)|=(336786389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6173889467/10000000000 : ℝ)|^131 ≤ (211310312223/400000000000 : ℝ)^99
        have hw : |(6173889467/10000000000 : ℝ)|=(6173889467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s4_s4_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7275876121/10000000000 : ℝ)*x 0 + (876645839/2000000000 : ℝ)*x 1 + (-126931027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7275876121/10000000000 : ℝ)^131 ≤ (65651123033479/100000000000000 : ℝ)^99 := by
    have hnat : (7275876121 : ℕ)^131*100000000000000^99 ≤ 65651123033479^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7275876121 10000000000 65651123033479 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (876645839/2000000000 : ℝ)^131 ≤ (8393642915781/25000000000000 : ℝ)^99 := by
    have hnat : (876645839 : ℕ)^131*25000000000000^99 ≤ 8393642915781^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876645839 2000000000 8393642915781 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126931027/5000000000 : ℝ)^131 ≤ (193576322639/25000000000000 : ℝ)^99 := by
    have hnat : (126931027 : ℕ)^131*25000000000000^99 ≤ 193576322639^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126931027 5000000000 193576322639 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7275876121/10000000000 : ℝ), (876645839/2000000000 : ℝ), (-126931027/5000000000 : ℝ)] ![(65651123033479/100000000000000 : ℝ), (8393642915781/25000000000000 : ℝ), (193576322639/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7275876121/10000000000 : ℝ)|^131 ≤ (65651123033479/100000000000000 : ℝ)^99
        have hw : |(7275876121/10000000000 : ℝ)|=(7275876121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(876645839/2000000000 : ℝ)|^131 ≤ (8393642915781/25000000000000 : ℝ)^99
        have hw : |(876645839/2000000000 : ℝ)|=(876645839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126931027/5000000000 : ℝ)|^131 ≤ (193576322639/25000000000000 : ℝ)^99
        have hw : |(-126931027/5000000000 : ℝ)|=(126931027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302059_s4_s4_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2004604513/10000000000 : ℝ)*x 0 + (3836124369/5000000000 : ℝ)*x 1 + (269629473/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2004604513/10000000000 : ℝ)^131 ≤ (11923995957453/100000000000000 : ℝ)^99 := by
    have hnat : (2004604513 : ℕ)^131*100000000000000^99 ≤ 11923995957453^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004604513 10000000000 11923995957453 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3836124369/5000000000 : ℝ)^131 ≤ (35212427634191/50000000000000 : ℝ)^99 := by
    have hnat : (3836124369 : ℕ)^131*50000000000000^99 ≤ 35212427634191^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3836124369 5000000000 35212427634191 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269629473/1000000000 : ℝ)^131 ≤ (17651148760399/100000000000000 : ℝ)^99 := by
    have hnat : (269629473 : ℕ)^131*100000000000000^99 ≤ 17651148760399^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269629473 1000000000 17651148760399 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2004604513/10000000000 : ℝ), (3836124369/5000000000 : ℝ), (269629473/1000000000 : ℝ)] ![(11923995957453/100000000000000 : ℝ), (35212427634191/50000000000000 : ℝ), (17651148760399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2004604513/10000000000 : ℝ)|^131 ≤ (11923995957453/100000000000000 : ℝ)^99
        have hw : |(2004604513/10000000000 : ℝ)|=(2004604513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3836124369/5000000000 : ℝ)|^131 ≤ (35212427634191/50000000000000 : ℝ)^99
        have hw : |(3836124369/5000000000 : ℝ)|=(3836124369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269629473/1000000000 : ℝ)|^131 ≤ (17651148760399/100000000000000 : ℝ)^99
        have hw : |(269629473/1000000000 : ℝ)|=(269629473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302059_s4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((76593/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76593/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75053/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75053/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(26023/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(26023/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((559/1000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(559/1000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53747/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(53747/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(11993/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(11993/50000 : ℝ)*X 1 2) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (76593/100000 : ℝ) ^ (65/16 : ℝ) ≤ (1353873632522022221/4000000000000000000 : ℝ) := by
    have hpowers : (76593/100000 : ℝ)^65 ≤ (1353873632522022221/4000000000000000000 : ℝ)^16 := by
      have hnat : (76593 : ℕ)^65*4000000000000000000^16 ≤ 1353873632522022221^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76593 100000 1353873632522022221 4000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (76593/100000 : ℝ)) (X := (1353873632522022221/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner0a : (5353873632522022221/4000000000000000000 : ℝ) ≤ (1342997146548809/1250000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (5353873632522022221/4000000000000000000 : ℝ)^16 ≤ (1342997146548809/1250000000000000 : ℝ)^65 := by
      have hnat : (5353873632522022221 : ℕ)^16*1250000000000000^65 ≤ 1342997146548809^65*4000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5353873632522022221 4000000000000000000 1342997146548809 1250000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1342997146548809/1250000000000000 : ℝ)) (X := (5353873632522022221/4000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner0b : (3353873632522022221/2000000000000000000 : ℝ) ≤ (11357052911202453/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3353873632522022221/2000000000000000000 : ℝ)^16 ≤ (11357052911202453/10000000000000000 : ℝ)^65 := by
      have hnat : (3353873632522022221 : ℕ)^16*10000000000000000^65 ≤ 11357052911202453^65*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3353873632522022221 2000000000000000000 11357052911202453 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11357052911202453/10000000000000000 : ℝ)) (X := (3353873632522022221/2000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(30999048849603/319137500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(613075738811981/7659300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (76593/100000 : ℝ)) (alpha := (30999048849603/319137500000000 : ℝ)) (beta := (613075738811981/7659300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (76593/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(30999048849603/319137500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(613075738811981/7659300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (75053/100000 : ℝ) ^ (65/16 : ℝ) ≤ (3895764917163675539/12500000000000000000 : ℝ) := by
    have hpowers : (75053/100000 : ℝ)^65 ≤ (3895764917163675539/12500000000000000000 : ℝ)^16 := by
      have hnat : (75053 : ℕ)^65*12500000000000000000^16 ≤ 3895764917163675539^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75053 100000 3895764917163675539 12500000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75053/100000 : ℝ)) (X := (3895764917163675539/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner1a : (16395764917163675539/12500000000000000000 : ℝ) ≤ (2672651088665787/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (16395764917163675539/12500000000000000000 : ℝ)^16 ≤ (2672651088665787/2500000000000000 : ℝ)^65 := by
      have hnat : (16395764917163675539 : ℕ)^16*2500000000000000^65 ≤ 2672651088665787^65*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16395764917163675539 12500000000000000000 2672651088665787 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2672651088665787/2500000000000000 : ℝ)) (X := (16395764917163675539/12500000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner1b : (10145764917163675539/6250000000000000000 : ℝ) ≤ (11266575862600299/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (10145764917163675539/6250000000000000000 : ℝ)^16 ≤ (11266575862600299/10000000000000000 : ℝ)^65 := by
      have hnat : (10145764917163675539 : ℕ)^16*10000000000000000^65 ≤ 11266575862600299^65*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10145764917163675539 6250000000000000000 11266575862600299 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266575862600299/10000000000000000 : ℝ)) (X := (10145764917163675539/6250000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(172651088665787/1876325000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(575971507937151/7505300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (75053/100000 : ℝ)) (alpha := (172651088665787/1876325000000000 : ℝ)) (beta := (575971507937151/7505300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (75053/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(172651088665787/1876325000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(575971507937151/7505300000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (26023/50000 : ℝ) ^ (65/16 : ℝ) ≤ (3522034807774298387/50000000000000000000 : ℝ) := by
    have hpowers : (26023/50000 : ℝ)^65 ≤ (3522034807774298387/50000000000000000000 : ℝ)^16 := by
      have hnat : (26023 : ℕ)^65*50000000000000000000^16 ≤ 3522034807774298387^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26023 50000 3522034807774298387 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26023/50000 : ℝ)) (X := (3522034807774298387/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner2a : (53522034807774298387/50000000000000000000 : ℝ) ≤ (635560602310689/625000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (53522034807774298387/50000000000000000000 : ℝ)^16 ≤ (635560602310689/625000000000000 : ℝ)^65 := by
      have hnat : (53522034807774298387 : ℕ)^16*625000000000000^65 ≤ 635560602310689^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53522034807774298387 50000000000000000000 635560602310689 625000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (635560602310689/625000000000000 : ℝ)) (X := (53522034807774298387/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner2b : (28522034807774298387/25000000000000000000 : ℝ) ≤ (5164876874091521/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (28522034807774298387/25000000000000000000 : ℝ)^16 ≤ (5164876874091521/5000000000000000 : ℝ)^65 := by
      have hnat : (28522034807774298387 : ℕ)^16*5000000000000000^65 ≤ 5164876874091521^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28522034807774298387 25000000000000000000 5164876874091521 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5164876874091521/5000000000000000 : ℝ)) (X := (28522034807774298387/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(10560602310689/325287500000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(80392055606009/2602300000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (26023/50000 : ℝ)) (alpha := (10560602310689/325287500000000 : ℝ)) (beta := (80392055606009/2602300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (26023/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(10560602310689/325287500000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(80392055606009/2602300000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_2 : ((6013888471/10000000000 : ℝ)*X 2 0+(5577647341/10000000000 : ℝ)*X 2 1+(-334580357/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((4199983631/10000000000 : ℝ)*X 0 0+(5153301069/10000000000 : ℝ)*X 0 1+(920991963/2500000000 : ℝ)*X 0 2+(4199983631/10000000000 : ℝ)*X 1 0+(5153301069/10000000000 : ℝ)*X 1 1+(920991963/2500000000 : ℝ)*X 1 2+(4199983631/10000000000 : ℝ)*X 2 0+(5153301069/10000000000 : ℝ)*X 2 1+(920991963/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-3028284013/10000000000 : ℝ)*X 0 0+(21470771/78125000 : ℝ)*X 0 1+(6909660833/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((121898463/400000000 : ℝ)*X 1 0+(-2694811553/10000000000 : ℝ)*X 1 1+(6934490847/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((2807232437/5000000000 : ℝ)*X 2 0+(778069721/1250000000 : ℝ)*X 2 1+(-9263681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((3660099349/10000000000 : ℝ)*X 0 0+(6692422761/10000000000 : ℝ)*X 0 1+(589284761/2500000000 : ℝ)*X 0 2+(3660099349/10000000000 : ℝ)*X 1 0+(6692422761/10000000000 : ℝ)*X 1 1+(589284761/2500000000 : ℝ)*X 1 2+(3660099349/10000000000 : ℝ)*X 2 0+(6692422761/10000000000 : ℝ)*X 2 1+(589284761/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-548404211/2000000000 : ℝ)*X 0 0+(759065761/2500000000 : ℝ)*X 0 1+(3454087573/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((2723749991/10000000000 : ℝ)*X 1 0+(-604301129/2000000000 : ℝ)*X 1 1+(6933004563/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((6651090339/10000000000 : ℝ)*X 2 0+(5162476901/10000000000 : ℝ)*X 2 1+(-10748557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_19 : ((-457/2500000000 : ℝ)*X 0 0+(457/2500000000 : ℝ)*X 0 1+(9999999981/10000000000 : ℝ)*X 0 2+(-457/2500000000 : ℝ)*X 1 0+(457/2500000000 : ℝ)*X 1 1+(9999999981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s4_s4_19 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((5801414333/10000000000 : ℝ)*X 0 0+(4673612429/10000000000 : ℝ)*X 0 1+(118004263/500000000 : ℝ)*X 0 2+(5801414333/10000000000 : ℝ)*X 1 0+(4673612429/10000000000 : ℝ)*X 1 1+(118004263/500000000 : ℝ)*X 1 2+(5801414333/10000000000 : ℝ)*X 2 0+(4673612429/10000000000 : ℝ)*X 2 1+(118004263/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-1704959659/5000000000 : ℝ)*X 0 0+(3422523759/10000000000 : ℝ)*X 0 1+(6075458739/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((3345360897/10000000000 : ℝ)*X 1 0+(-336786389/1000000000 : ℝ)*X 1 1+(6173889467/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((7275876121/10000000000 : ℝ)*X 2 0+(876645839/2000000000 : ℝ)*X 2 1+(-126931027/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((2004604513/10000000000 : ℝ)*X 0 0+(3836124369/5000000000 : ℝ)*X 0 1+(269629473/1000000000 : ℝ)*X 0 2+(2004604513/10000000000 : ℝ)*X 1 0+(3836124369/5000000000 : ℝ)*X 1 1+(269629473/1000000000 : ℝ)*X 1 2+(2004604513/10000000000 : ℝ)*X 2 0+(3836124369/5000000000 : ℝ)*X 2 1+(269629473/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302059_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((559/1000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(559/1000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3419172517648837214225172982133/226657744614950000000000000000000000 : ℝ) := by norm_num
    linear_combination (1975733/1000000000000 : ℝ)*(base13) + (605201170197/500000000000 : ℝ)*(base60) + (5582160665311/1000000000000 : ℝ)*(major_s4_0) + (5582160665311/1000000000000 : ℝ)*(major_s4_1) + (1116463915593/200000000000 : ℝ)*(major_s4_2) + (37999293/1000000000000 : ℝ)*(sp_s4_2) + (5985337/1000000000000 : ℝ)*(sp_s4_6) + (463885458517/62500000000 : ℝ)*(sp_s4_7) + (371099815293/50000000000 : ℝ)*(sp_s4_8) + (7422131312711/1000000000000 : ℝ)*(sp_s4_9) + (3742084091081/1000000000000 : ℝ)*(sp_s4_13) + (34601229/200000000000 : ℝ)*(sp_s4_15) + (79456327/500000000000 : ℝ)*(sp_s4_19) + (28456901/500000000000 : ℝ)*(sp_s4_27) + (187107349511/50000000000 : ℝ)*(f.failure) + (1855542328001/250000000000 : ℝ)*(f.sum) + (4191698429721392591/12206901368750000000000000000000 : ℝ)*base62 + (269379183100891/520460000000000000000000000 : ℝ)*base64 + (3281106539088979/7505300000000000000000000000 : ℝ)*base66 + (168928712582883/260230000000000000000000000 : ℝ)*base68 + (15844840537443371203/66439321300000000000000000000000 : ℝ)*base70 + (3132055397776519/7659300000000000000000000000 : ℝ)*base72 + (559489456598379/3752650000000000000000000000 : ℝ)*base75 + (306102707970327/1276550000000000000000000000 : ℝ)*base77 + (939730967359497557/26129701950000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (87/500000000000000 : ℝ)*base87 + (87/500000000000000 : ℝ)*base89 + (87/500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53747/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(53747/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (665543289246350003307/52046000000000000000000000 : ℝ) := by norm_num
    linear_combination (105889/200000000000 : ℝ)*(base13) + (2465807/1000000000000 : ℝ)*(base53) + (1194342567067/1000000000000 : ℝ)*(base60) + (5517474385949/1000000000000 : ℝ)*(major_s4_0) + (5517474385949/1000000000000 : ℝ)*(major_s4_1) + (220703295501/40000000000 : ℝ)*(major_s4_2) + (7708893/500000000000 : ℝ)*(sp_s4_6) + (153998621/1000000000000 : ℝ)*(sp_s4_7) + (7336004659721/1000000000000 : ℝ)*(sp_s4_14) + (7336159187787/1000000000000 : ℝ)*(sp_s4_15) + (3668034790203/500000000000 : ℝ)*(sp_s4_16) + (110467383/1000000000000 : ℝ)*(sp_s4_19) + (1849383718991/500000000000 : ℝ)*(sp_s4_20) + (92073187/1000000000000 : ℝ)*(sp_s4_23) + (462347856971/125000000000 : ℝ)*(f.failure) + (3668080826797/500000000000 : ℝ)*(f.sum) + (20015604930036238201/48827605475000000000000000000000 : ℝ)*base62 + (20906123318423/520460000000000000000000000 : ℝ)*base64 + (205026390266079/7505300000000000000000000000 : ℝ)*base67 + (104215891451/2081840000000000000000000 : ℝ)*base68 + (27887399925696944307/66439321300000000000000000000000 : ℝ)*base70 + (244914592214689/7659300000000000000000000000 : ℝ)*base73 + (2928718812386981/3752650000000000000000000000 : ℝ)*base75 + (777188681274123/1276550000000000000000000000 : ℝ)*base77 + (467241623765775607/6532425487500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (157/1250000000000000 : ℝ)*base87 + (157/1250000000000000 : ℝ)*base89 + (157/1250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(11993/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(11993/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2383494659361187880778830917/321957023600781250000000000000000 : ℝ) := by norm_num
    linear_combination (703379/1000000000000 : ℝ)*(base8) + (2832457/1000000000000 : ℝ)*(base11) + (29943957789/1000000000000 : ℝ)*(base50) + (2939992119/15625000000 : ℝ)*(base60) + (3059584079629/1000000000000 : ℝ)*(major_s4_0) + (3059584079629/1000000000000 : ℝ)*(major_s4_1) + (3059584079629/1000000000000 : ℝ)*(major_s4_2) + (29329083/1000000000000 : ℝ)*(sp_s4_2) + (65594063/1000000000000 : ℝ)*(sp_s4_13) + (51071473/1000000000000 : ℝ)*(sp_s4_16) + (508511271371/125000000000 : ℝ)*(sp_s4_21) + (1017023426701/250000000000 : ℝ)*(sp_s4_22) + (4068013306247/1000000000000 : ℝ)*(sp_s4_23) + (128187899417/62500000000 : ℝ)*(sp_s4_27) + (410214396947/200000000000 : ℝ)*(f.failure) + (1017023426701/250000000000 : ℝ)*(f.sum) + (3267573992435725171/8877746450000000000000000000000 : ℝ)*base63 + (618719460545269/2602300000000000000000000000 : ℝ)*base64 + (236854728523231/682300000000000000000000000 : ℝ)*base66 + (403721164602289/1301150000000000000000000000 : ℝ)*base68 + (883858932695226061/6039938300000000000000000000000 : ℝ)*base70 + (197173881583541/696300000000000000000000000 : ℝ)*base72 + (45895225725859/85287500000000000000000000 : ℝ)*base75 + (5602048687467/29012500000000000000000000 : ℝ)*base77 + (575011526829714163/2375427450000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (399/2000000000000000 : ℝ)*base87 + (399/2000000000000000 : ℝ)*base89 + (399/2000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((76593/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76593/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75053/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75053/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(26023/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(26023/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((559/1000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(559/1000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53747/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(53747/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(11993/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(11993/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302059_s4 p hpa hpb X hX hprev3

#print axioms solution

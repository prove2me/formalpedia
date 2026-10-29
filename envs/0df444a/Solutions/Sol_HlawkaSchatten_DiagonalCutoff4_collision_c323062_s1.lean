-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c323062_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:53:28.641059+00:00
-- url     : https://prove2.me/submissions/10f87c2e-c2ae-429f-84b7-adf163678c0b

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
theorem collision_support_c323062_s1_s1_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-737671011/5000000000 : ℝ)*x 0 + (4961049663/10000000000 : ℝ)*x 1 + (-5569356467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (737671011/5000000000 : ℝ)^21 ≤ (2351137699933/25000000000000 : ℝ)^17 := by
    have hnat : (737671011 : ℕ)^21*25000000000000^17 ≤ 2351137699933^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737671011 5000000000 2351137699933 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4961049663/10000000000 : ℝ)^21 ≤ (42067221424379/100000000000000 : ℝ)^17 := by
    have hnat : (4961049663 : ℕ)^21*100000000000000^17 ≤ 42067221424379^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4961049663 10000000000 42067221424379 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5569356467/10000000000 : ℝ)^21 ≤ (9705645552993/20000000000000 : ℝ)^17 := by
    have hnat : (5569356467 : ℕ)^21*20000000000000^17 ≤ 9705645552993^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5569356467 10000000000 9705645552993 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-737671011/5000000000 : ℝ), (4961049663/10000000000 : ℝ), (-5569356467/10000000000 : ℝ)] ![(2351137699933/25000000000000 : ℝ), (42067221424379/100000000000000 : ℝ), (9705645552993/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-737671011/5000000000 : ℝ)|^21 ≤ (2351137699933/25000000000000 : ℝ)^17
        have hw : |(-737671011/5000000000 : ℝ)|=(737671011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4961049663/10000000000 : ℝ)|^21 ≤ (42067221424379/100000000000000 : ℝ)^17
        have hw : |(4961049663/10000000000 : ℝ)|=(4961049663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5569356467/10000000000 : ℝ)|^21 ≤ (9705645552993/20000000000000 : ℝ)^17
        have hw : |(-5569356467/10000000000 : ℝ)|=(5569356467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323062_s1_s1_1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2483176837/5000000000 : ℝ)*x 0 + (-737401963/5000000000 : ℝ)*x 1 + (-1112917473/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2483176837/5000000000 : ℝ)^21 ≤ (10530696552707/25000000000000 : ℝ)^17 := by
    have hnat : (2483176837 : ℕ)^21*25000000000000^17 ≤ 10530696552707^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2483176837 5000000000 10530696552707 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (737401963/5000000000 : ℝ)^21 ≤ (4700156907769/50000000000000 : ℝ)^17 := by
    have hnat : (737401963 : ℕ)^21*50000000000000^17 ≤ 4700156907769^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737401963 5000000000 4700156907769 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1112917473/2000000000 : ℝ)^21 ≤ (378725780989/781250000000 : ℝ)^17 := by
    have hnat : (1112917473 : ℕ)^21*781250000000^17 ≤ 378725780989^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112917473 2000000000 378725780989 781250000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2483176837/5000000000 : ℝ), (-737401963/5000000000 : ℝ), (-1112917473/2000000000 : ℝ)] ![(10530696552707/25000000000000 : ℝ), (4700156907769/50000000000000 : ℝ), (378725780989/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2483176837/5000000000 : ℝ)|^21 ≤ (10530696552707/25000000000000 : ℝ)^17
        have hw : |(2483176837/5000000000 : ℝ)|=(2483176837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-737401963/5000000000 : ℝ)|^21 ≤ (4700156907769/50000000000000 : ℝ)^17
        have hw : |(-737401963/5000000000 : ℝ)|=(737401963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1112917473/2000000000 : ℝ)|^21 ≤ (378725780989/781250000000 : ℝ)^17
        have hw : |(-1112917473/2000000000 : ℝ)|=(1112917473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323062_s1_s1_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2544977671/5000000000 : ℝ)*x 0 + (2548275651/5000000000 : ℝ)*x 1 + (481959273/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2544977671/5000000000 : ℝ)^21 ≤ (43421567253063/100000000000000 : ℝ)^17 := by
    have hnat : (2544977671 : ℕ)^21*100000000000000^17 ≤ 43421567253063^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2544977671 5000000000 43421567253063 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2548275651/5000000000 : ℝ)^21 ≤ (43491086665587/100000000000000 : ℝ)^17 := by
    have hnat : (2548275651 : ℕ)^21*100000000000000^17 ≤ 43491086665587^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548275651 5000000000 43491086665587 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (481959273/2500000000 : ℝ)^21 ≤ (6543673032751/50000000000000 : ℝ)^17 := by
    have hnat : (481959273 : ℕ)^21*50000000000000^17 ≤ 6543673032751^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481959273 2500000000 6543673032751 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2544977671/5000000000 : ℝ), (2548275651/5000000000 : ℝ), (481959273/2500000000 : ℝ)] ![(43421567253063/100000000000000 : ℝ), (43491086665587/100000000000000 : ℝ), (6543673032751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2544977671/5000000000 : ℝ)|^21 ≤ (43421567253063/100000000000000 : ℝ)^17
        have hw : |(2544977671/5000000000 : ℝ)|=(2544977671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2548275651/5000000000 : ℝ)|^21 ≤ (43491086665587/100000000000000 : ℝ)^17
        have hw : |(2548275651/5000000000 : ℝ)|=(2548275651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(481959273/2500000000 : ℝ)|^21 ≤ (6543673032751/50000000000000 : ℝ)^17
        have hw : |(481959273/2500000000 : ℝ)|=(481959273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323062_s1_s1_6 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2722391309/5000000000 : ℝ)*x 0 + (2721290287/5000000000 : ℝ)*x 1 + (-60970609/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2722391309/5000000000 : ℝ)^21 ≤ (47190906586459/100000000000000 : ℝ)^17 := by
    have hnat : (2722391309 : ℕ)^21*100000000000000^17 ≤ 47190906586459^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722391309 5000000000 47190906586459 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721290287/5000000000 : ℝ)^21 ≤ (2947958218137/6250000000000 : ℝ)^17 := by
    have hnat : (2721290287 : ℕ)^21*6250000000000^17 ≤ 2947958218137^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721290287 5000000000 2947958218137 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60970609/625000000 : ℝ)^21 ≤ (1128352382501/20000000000000 : ℝ)^17 := by
    have hnat : (60970609 : ℕ)^21*20000000000000^17 ≤ 1128352382501^17*625000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60970609 625000000 1128352382501 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2722391309/5000000000 : ℝ), (2721290287/5000000000 : ℝ), (-60970609/625000000 : ℝ)] ![(47190906586459/100000000000000 : ℝ), (2947958218137/6250000000000 : ℝ), (1128352382501/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2722391309/5000000000 : ℝ)|^21 ≤ (47190906586459/100000000000000 : ℝ)^17
        have hw : |(2722391309/5000000000 : ℝ)|=(2722391309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721290287/5000000000 : ℝ)|^21 ≤ (2947958218137/6250000000000 : ℝ)^17
        have hw : |(2721290287/5000000000 : ℝ)|=(2721290287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-60970609/625000000 : ℝ)|^21 ≤ (1128352382501/20000000000000 : ℝ)^17
        have hw : |(-60970609/625000000 : ℝ)|=(60970609/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323062_s1_s1_7 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-237182319/2000000000 : ℝ)*x 0 + (2299408997/5000000000 : ℝ)*x 1 + (-6119129661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (237182319/2000000000 : ℝ)^21 ≤ (3590478051039/50000000000000 : ℝ)^17 := by
    have hnat : (237182319 : ℕ)^21*50000000000000^17 ≤ 3590478051039^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237182319 2000000000 3590478051039 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2299408997/5000000000 : ℝ)^21 ≤ (38306181531657/100000000000000 : ℝ)^17 := by
    have hnat : (2299408997 : ℕ)^21*100000000000000^17 ≤ 38306181531657^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2299408997 5000000000 38306181531657 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6119129661/10000000000 : ℝ)^21 ≤ (54512862356477/100000000000000 : ℝ)^17 := by
    have hnat : (6119129661 : ℕ)^21*100000000000000^17 ≤ 54512862356477^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6119129661 10000000000 54512862356477 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-237182319/2000000000 : ℝ), (2299408997/5000000000 : ℝ), (-6119129661/10000000000 : ℝ)] ![(3590478051039/50000000000000 : ℝ), (38306181531657/100000000000000 : ℝ), (54512862356477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-237182319/2000000000 : ℝ)|^21 ≤ (3590478051039/50000000000000 : ℝ)^17
        have hw : |(-237182319/2000000000 : ℝ)|=(237182319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2299408997/5000000000 : ℝ)|^21 ≤ (38306181531657/100000000000000 : ℝ)^17
        have hw : |(2299408997/5000000000 : ℝ)|=(2299408997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6119129661/10000000000 : ℝ)|^21 ≤ (54512862356477/100000000000000 : ℝ)^17
        have hw : |(-6119129661/10000000000 : ℝ)|=(6119129661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323062_s1_s1_8 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4976052769/10000000000 : ℝ)*x 0 + (-97227159/1000000000 : ℝ)*x 1 + (-2952081439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4976052769/10000000000 : ℝ)^21 ≤ (5278053747307/12500000000000 : ℝ)^17 := by
    have hnat : (4976052769 : ℕ)^21*12500000000000^17 ≤ 5278053747307^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4976052769 10000000000 5278053747307 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97227159/1000000000 : ℝ)^21 ≤ (140462366109/2500000000000 : ℝ)^17 := by
    have hnat : (97227159 : ℕ)^21*2500000000000^17 ≤ 140462366109^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97227159 1000000000 140462366109 2500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2952081439/5000000000 : ℝ)^21 ≤ (10431415074007/20000000000000 : ℝ)^17 := by
    have hnat : (2952081439 : ℕ)^21*20000000000000^17 ≤ 10431415074007^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2952081439 5000000000 10431415074007 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4976052769/10000000000 : ℝ), (-97227159/1000000000 : ℝ), (-2952081439/5000000000 : ℝ)] ![(5278053747307/12500000000000 : ℝ), (140462366109/2500000000000 : ℝ), (10431415074007/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4976052769/10000000000 : ℝ)|^21 ≤ (5278053747307/12500000000000 : ℝ)^17
        have hw : |(4976052769/10000000000 : ℝ)|=(4976052769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-97227159/1000000000 : ℝ)|^21 ≤ (140462366109/2500000000000 : ℝ)^17
        have hw : |(-97227159/1000000000 : ℝ)|=(97227159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2952081439/5000000000 : ℝ)|^21 ≤ (10431415074007/20000000000000 : ℝ)^17
        have hw : |(-2952081439/5000000000 : ℝ)|=(2952081439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323062_s1_s1_9 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1225411177/2500000000 : ℝ)*x 0 + (2907915661/5000000000 : ℝ)*x 1 + (1209697103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1225411177/2500000000 : ℝ)^21 ≤ (41445853001719/100000000000000 : ℝ)^17 := by
    have hnat : (1225411177 : ℕ)^21*100000000000000^17 ≤ 41445853001719^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1225411177 2500000000 41445853001719 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2907915661/5000000000 : ℝ)^21 ≤ (12798714530151/25000000000000 : ℝ)^17 := by
    have hnat : (2907915661 : ℕ)^21*25000000000000^17 ≤ 12798714530151^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2907915661 5000000000 12798714530151 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1209697103/10000000000 : ℝ)^21 ≤ (1839822216527/25000000000000 : ℝ)^17 := by
    have hnat : (1209697103 : ℕ)^21*25000000000000^17 ≤ 1839822216527^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209697103 10000000000 1839822216527 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1225411177/2500000000 : ℝ), (2907915661/5000000000 : ℝ), (1209697103/10000000000 : ℝ)] ![(41445853001719/100000000000000 : ℝ), (12798714530151/25000000000000 : ℝ), (1839822216527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1225411177/2500000000 : ℝ)|^21 ≤ (41445853001719/100000000000000 : ℝ)^17
        have hw : |(1225411177/2500000000 : ℝ)|=(1225411177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2907915661/5000000000 : ℝ)|^21 ≤ (12798714530151/25000000000000 : ℝ)^17
        have hw : |(2907915661/5000000000 : ℝ)|=(2907915661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1209697103/10000000000 : ℝ)|^21 ≤ (1839822216527/25000000000000 : ℝ)^17
        have hw : |(1209697103/10000000000 : ℝ)|=(1209697103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323062_s1_s1_13 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5167485033/10000000000 : ℝ)*x 0 + (238413827/400000000 : ℝ)*x 1 + (-58332967/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5167485033/10000000000 : ℝ)^21 ≤ (44240040535419/100000000000000 : ℝ)^17 := by
    have hnat : (5167485033 : ℕ)^21*100000000000000^17 ≤ 44240040535419^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167485033 10000000000 44240040535419 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238413827/400000000 : ℝ)^21 ≤ (52770856285589/100000000000000 : ℝ)^17 := by
    have hnat : (238413827 : ℕ)^21*100000000000000^17 ≤ 52770856285589^17*400000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238413827 400000000 52770856285589 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58332967/1000000000 : ℝ)^21 ≤ (2989103174499/100000000000000 : ℝ)^17 := by
    have hnat : (58332967 : ℕ)^21*100000000000000^17 ≤ 2989103174499^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58332967 1000000000 2989103174499 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5167485033/10000000000 : ℝ), (238413827/400000000 : ℝ), (-58332967/1000000000 : ℝ)] ![(44240040535419/100000000000000 : ℝ), (52770856285589/100000000000000 : ℝ), (2989103174499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5167485033/10000000000 : ℝ)|^21 ≤ (44240040535419/100000000000000 : ℝ)^17
        have hw : |(5167485033/10000000000 : ℝ)|=(5167485033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(238413827/400000000 : ℝ)|^21 ≤ (52770856285589/100000000000000 : ℝ)^17
        have hw : |(238413827/400000000 : ℝ)|=(238413827/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-58332967/1000000000 : ℝ)|^21 ≤ (2989103174499/100000000000000 : ℝ)^17
        have hw : |(-58332967/1000000000 : ℝ)|=(58332967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323062_s1_s1_14 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-446087459/5000000000 : ℝ)*x 0 + (97551731/200000000 : ℝ)*x 1 + (-189061859/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (446087459/5000000000 : ℝ)^21 ≤ (5052392371129/100000000000000 : ℝ)^17 := by
    have hnat : (446087459 : ℕ)^21*100000000000000^17 ≤ 5052392371129^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446087459 5000000000 5052392371129 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97551731/200000000 : ℝ)^21 ≤ (1287334691907/3125000000000 : ℝ)^17 := by
    have hnat : (97551731 : ℕ)^21*3125000000000^17 ≤ 1287334691907^17*200000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97551731 200000000 1287334691907 3125000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (189061859/312500000 : ℝ)^21 ≤ (26876448734167/50000000000000 : ℝ)^17 := by
    have hnat : (189061859 : ℕ)^21*50000000000000^17 ≤ 26876448734167^17*312500000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189061859 312500000 26876448734167 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-446087459/5000000000 : ℝ), (97551731/200000000 : ℝ), (-189061859/312500000 : ℝ)] ![(5052392371129/100000000000000 : ℝ), (1287334691907/3125000000000 : ℝ), (26876448734167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-446087459/5000000000 : ℝ)|^21 ≤ (5052392371129/100000000000000 : ℝ)^17
        have hw : |(-446087459/5000000000 : ℝ)|=(446087459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(97551731/200000000 : ℝ)|^21 ≤ (1287334691907/3125000000000 : ℝ)^17
        have hw : |(97551731/200000000 : ℝ)|=(97551731/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-189061859/312500000 : ℝ)|^21 ≤ (26876448734167/50000000000000 : ℝ)^17
        have hw : |(-189061859/312500000 : ℝ)|=(189061859/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323062_s1_s1_15 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4708821427/10000000000 : ℝ)*x 0 + (-128445513/1000000000 : ℝ)*x 1 + (-594779793/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4708821427/10000000000 : ℝ)^21 ≤ (19720612292769/50000000000000 : ℝ)^17 := by
    have hnat : (4708821427 : ℕ)^21*50000000000000^17 ≤ 19720612292769^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4708821427 10000000000 19720612292769 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128445513/1000000000 : ℝ)^21 ≤ (1585023633419/20000000000000 : ℝ)^17 := by
    have hnat : (128445513 : ℕ)^21*20000000000000^17 ≤ 1585023633419^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128445513 1000000000 1585023633419 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (594779793/1000000000 : ℝ)^21 ≤ (657920715391/1250000000000 : ℝ)^17 := by
    have hnat : (594779793 : ℕ)^21*1250000000000^17 ≤ 657920715391^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594779793 1000000000 657920715391 1250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4708821427/10000000000 : ℝ), (-128445513/1000000000 : ℝ), (-594779793/1000000000 : ℝ)] ![(19720612292769/50000000000000 : ℝ), (1585023633419/20000000000000 : ℝ), (657920715391/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4708821427/10000000000 : ℝ)|^21 ≤ (19720612292769/50000000000000 : ℝ)^17
        have hw : |(4708821427/10000000000 : ℝ)|=(4708821427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128445513/1000000000 : ℝ)|^21 ≤ (1585023633419/20000000000000 : ℝ)^17
        have hw : |(-128445513/1000000000 : ℝ)|=(128445513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-594779793/1000000000 : ℝ)|^21 ≤ (657920715391/1250000000000 : ℝ)^17
        have hw : |(-594779793/1000000000 : ℝ)|=(594779793/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323062_s1_s1_16 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (569149747/1000000000 : ℝ)*x 0 + (1253367659/2500000000 : ℝ)*x 1 + (308313421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (569149747/1000000000 : ℝ)^21 ≤ (24923142342209/50000000000000 : ℝ)^17 := by
    have hnat : (569149747 : ℕ)^21*50000000000000^17 ≤ 24923142342209^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569149747 1000000000 24923142342209 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1253367659/2500000000 : ℝ)^21 ≤ (21308497462403/50000000000000 : ℝ)^17 := by
    have hnat : (1253367659 : ℕ)^21*50000000000000^17 ≤ 21308497462403^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253367659 2500000000 21308497462403 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (308313421/2500000000 : ℝ)^21 ≤ (7536720383267/100000000000000 : ℝ)^17 := by
    have hnat : (308313421 : ℕ)^21*100000000000000^17 ≤ 7536720383267^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308313421 2500000000 7536720383267 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(569149747/1000000000 : ℝ), (1253367659/2500000000 : ℝ), (308313421/2500000000 : ℝ)] ![(24923142342209/50000000000000 : ℝ), (21308497462403/50000000000000 : ℝ), (7536720383267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(569149747/1000000000 : ℝ)|^21 ≤ (24923142342209/50000000000000 : ℝ)^17
        have hw : |(569149747/1000000000 : ℝ)|=(569149747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1253367659/2500000000 : ℝ)|^21 ≤ (21308497462403/50000000000000 : ℝ)^17
        have hw : |(1253367659/2500000000 : ℝ)|=(1253367659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(308313421/2500000000 : ℝ)|^21 ≤ (7536720383267/100000000000000 : ℝ)^17
        have hw : |(308313421/2500000000 : ℝ)|=(308313421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323062_s1_s1_20 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3117688819/5000000000 : ℝ)*x 0 + (2438071491/5000000000 : ℝ)*x 1 + (-589051523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3117688819/5000000000 : ℝ)^21 ≤ (55794986328969/100000000000000 : ℝ)^17 := by
    have hnat : (3117688819 : ℕ)^21*100000000000000^17 ≤ 55794986328969^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117688819 5000000000 55794986328969 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2438071491/5000000000 : ℝ)^21 ≤ (41179650002601/100000000000000 : ℝ)^17 := by
    have hnat : (2438071491 : ℕ)^21*100000000000000^17 ≤ 41179650002601^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2438071491 5000000000 41179650002601 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (589051523/10000000000 : ℝ)^21 ≤ (3025363654341/100000000000000 : ℝ)^17 := by
    have hnat : (589051523 : ℕ)^21*100000000000000^17 ≤ 3025363654341^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589051523 10000000000 3025363654341 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3117688819/5000000000 : ℝ), (2438071491/5000000000 : ℝ), (-589051523/10000000000 : ℝ)] ![(55794986328969/100000000000000 : ℝ), (41179650002601/100000000000000 : ℝ), (3025363654341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3117688819/5000000000 : ℝ)|^21 ≤ (55794986328969/100000000000000 : ℝ)^17
        have hw : |(3117688819/5000000000 : ℝ)|=(3117688819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2438071491/5000000000 : ℝ)|^21 ≤ (41179650002601/100000000000000 : ℝ)^17
        have hw : |(2438071491/5000000000 : ℝ)|=(2438071491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-589051523/10000000000 : ℝ)|^21 ≤ (3025363654341/100000000000000 : ℝ)^17
        have hw : |(-589051523/10000000000 : ℝ)|=(589051523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323062_s1_s1_21 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-707325123/10000000000 : ℝ)*x 0 + (1052877379/2000000000 : ℝ)*x 1 + (-23169631/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (707325123/10000000000 : ℝ)^21 ≤ (1896318253407/50000000000000 : ℝ)^17 := by
    have hnat : (707325123 : ℕ)^21*50000000000000^17 ≤ 1896318253407^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707325123 10000000000 1896318253407 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052877379/2000000000 : ℝ)^21 ≤ (11316772472019/25000000000000 : ℝ)^17 := by
    have hnat : (1052877379 : ℕ)^21*25000000000000^17 ≤ 11316772472019^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052877379 2000000000 11316772472019 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23169631/40000000 : ℝ)^21 ≤ (6367534199789/12500000000000 : ℝ)^17 := by
    have hnat : (23169631 : ℕ)^21*12500000000000^17 ≤ 6367534199789^17*40000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23169631 40000000 6367534199789 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-707325123/10000000000 : ℝ), (1052877379/2000000000 : ℝ), (-23169631/40000000 : ℝ)] ![(1896318253407/50000000000000 : ℝ), (11316772472019/25000000000000 : ℝ), (6367534199789/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-707325123/10000000000 : ℝ)|^21 ≤ (1896318253407/50000000000000 : ℝ)^17
        have hw : |(-707325123/10000000000 : ℝ)|=(707325123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052877379/2000000000 : ℝ)|^21 ≤ (11316772472019/25000000000000 : ℝ)^17
        have hw : |(1052877379/2000000000 : ℝ)|=(1052877379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-23169631/40000000 : ℝ)|^21 ≤ (6367534199789/12500000000000 : ℝ)^17
        have hw : |(-23169631/40000000 : ℝ)|=(23169631/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323062_s1_s1_22 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5752400071/10000000000 : ℝ)*x 0 + (-594739817/5000000000 : ℝ)*x 1 + (-4981958611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5752400071/10000000000 : ℝ)^21 ≤ (50506001215017/100000000000000 : ℝ)^17 := by
    have hnat : (5752400071 : ℕ)^21*100000000000000^17 ≤ 50506001215017^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5752400071 10000000000 50506001215017 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (594739817/5000000000 : ℝ)^21 ≤ (7207654395519/100000000000000 : ℝ)^17 := by
    have hnat : (594739817 : ℕ)^21*100000000000000^17 ≤ 7207654395519^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594739817 5000000000 7207654395519 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4981958611/10000000000 : ℝ)^21 ≤ (10571586093359/25000000000000 : ℝ)^17 := by
    have hnat : (4981958611 : ℕ)^21*25000000000000^17 ≤ 10571586093359^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4981958611 10000000000 10571586093359 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5752400071/10000000000 : ℝ), (-594739817/5000000000 : ℝ), (-4981958611/10000000000 : ℝ)] ![(50506001215017/100000000000000 : ℝ), (7207654395519/100000000000000 : ℝ), (10571586093359/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5752400071/10000000000 : ℝ)|^21 ≤ (50506001215017/100000000000000 : ℝ)^17
        have hw : |(5752400071/10000000000 : ℝ)|=(5752400071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-594739817/5000000000 : ℝ)|^21 ≤ (7207654395519/100000000000000 : ℝ)^17
        have hw : |(-594739817/5000000000 : ℝ)|=(594739817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4981958611/10000000000 : ℝ)|^21 ≤ (10571586093359/25000000000000 : ℝ)^17
        have hw : |(-4981958611/10000000000 : ℝ)|=(4981958611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323062_s1_s1_23 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (954931907/2000000000 : ℝ)*x 0 + (5400267773/10000000000 : ℝ)*x 1 + (1936695723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (954931907/2000000000 : ℝ)^21 ≤ (10030889701961/25000000000000 : ℝ)^17 := by
    have hnat : (954931907 : ℕ)^21*25000000000000^17 ≤ 10030889701961^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954931907 2000000000 10030889701961 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400267773/10000000000 : ℝ)^21 ≤ (46714767083329/100000000000000 : ℝ)^17 := by
    have hnat : (5400267773 : ℕ)^21*100000000000000^17 ≤ 46714767083329^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400267773 10000000000 46714767083329 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1936695723/10000000000 : ℝ)^21 ≤ (13161674105767/100000000000000 : ℝ)^17 := by
    have hnat : (1936695723 : ℕ)^21*100000000000000^17 ≤ 13161674105767^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936695723 10000000000 13161674105767 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(954931907/2000000000 : ℝ), (5400267773/10000000000 : ℝ), (1936695723/10000000000 : ℝ)] ![(10030889701961/25000000000000 : ℝ), (46714767083329/100000000000000 : ℝ), (13161674105767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(954931907/2000000000 : ℝ)|^21 ≤ (10030889701961/25000000000000 : ℝ)^17
        have hw : |(954931907/2000000000 : ℝ)|=(954931907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400267773/10000000000 : ℝ)|^21 ≤ (46714767083329/100000000000000 : ℝ)^17
        have hw : |(5400267773/10000000000 : ℝ)|=(5400267773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1936695723/10000000000 : ℝ)|^21 ≤ (13161674105767/100000000000000 : ℝ)^17
        have hw : |(1936695723/10000000000 : ℝ)|=(1936695723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323062_s1_s1_27 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (640463249/1000000000 : ℝ)*x 0 + (4599499951/10000000000 : ℝ)*x 1 + (-740714909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (640463249/1000000000 : ℝ)^21 ≤ (3604486957059/6250000000000 : ℝ)^17 := by
    have hnat : (640463249 : ℕ)^21*6250000000000^17 ≤ 3604486957059^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640463249 1000000000 3604486957059 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4599499951/10000000000 : ℝ)^21 ≤ (383131986303/1000000000000 : ℝ)^17 := by
    have hnat : (4599499951 : ℕ)^21*1000000000000^17 ≤ 383131986303^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4599499951 10000000000 383131986303 1000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (740714909/10000000000 : ℝ)^21 ≤ (125469063813/3125000000000 : ℝ)^17 := by
    have hnat : (740714909 : ℕ)^21*3125000000000^17 ≤ 125469063813^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740714909 10000000000 125469063813 3125000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(640463249/1000000000 : ℝ), (4599499951/10000000000 : ℝ), (-740714909/10000000000 : ℝ)] ![(3604486957059/6250000000000 : ℝ), (383131986303/1000000000000 : ℝ), (125469063813/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(640463249/1000000000 : ℝ)|^21 ≤ (3604486957059/6250000000000 : ℝ)^17
        have hw : |(640463249/1000000000 : ℝ)|=(640463249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4599499951/10000000000 : ℝ)|^21 ≤ (383131986303/1000000000000 : ℝ)^17
        have hw : |(4599499951/10000000000 : ℝ)|=(4599499951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-740714909/10000000000 : ℝ)|^21 ≤ (125469063813/3125000000000 : ℝ)^17
        have hw : |(-740714909/10000000000 : ℝ)|=(740714909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c323062_s1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((3463/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3463/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34431/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34431/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29203/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29203/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((33731/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33731/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33983/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33983/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5309/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5309/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80913/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80913/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s1_pow0 : (3463/5000 : ℝ) ^ (83/16 : ℝ) ≤ (7438286580809436843/50000000000000000000 : ℝ) := by
    have hpowers : (3463/5000 : ℝ)^83 ≤ (7438286580809436843/50000000000000000000 : ℝ)^16 := by
      have hnat : (3463 : ℕ)^83*50000000000000000000^16 ≤ 7438286580809436843^16*5000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3463 5000 7438286580809436843 50000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3463/5000 : ℝ)) (X := (7438286580809436843/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (57438286580809436843/50000000000000000000 : ℝ) ≤ (10270956411402891/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (57438286580809436843/50000000000000000000 : ℝ)^16 ≤ (10270956411402891/10000000000000000 : ℝ)^83 := by
      have hnat : (57438286580809436843 : ℕ)^16*10000000000000000^83 ≤ 10270956411402891^83*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57438286580809436843 50000000000000000000 10270956411402891 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10270956411402891/10000000000000000 : ℝ)) (X := (57438286580809436843/50000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (32438286580809436843/25000000000000000000 : ℝ) ≤ (10514917263339517/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (32438286580809436843/25000000000000000000 : ℝ)^16 ≤ (10514917263339517/10000000000000000 : ℝ)^83 := by
      have hnat : (32438286580809436843 : ℕ)^16*10000000000000000^83 ≤ 10514917263339517^83*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32438286580809436843 25000000000000000000 10514917263339517 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10514917263339517/10000000000000000 : ℝ)) (X := (32438286580809436843/25000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(270956411402891/6926000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(121980425968313/3463000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (3463/5000 : ℝ)) (alpha := (270956411402891/6926000000000000 : ℝ)) (beta := (121980425968313/3463000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (3463/5000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(270956411402891/6926000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(121980425968313/3463000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (34431/50000 : ℝ) ^ (83/16 : ℝ) ≤ (14438409037251435061/100000000000000000000 : ℝ) := by
    have hpowers : (34431/50000 : ℝ)^83 ≤ (14438409037251435061/100000000000000000000 : ℝ)^16 := by
      have hnat : (34431 : ℕ)^83*100000000000000000000^16 ≤ 14438409037251435061^16*50000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34431 50000 14438409037251435061 100000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34431/50000 : ℝ)) (X := (14438409037251435061/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (114438409037251435061/100000000000000000000 : ℝ) ≤ (10263392825757491/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (114438409037251435061/100000000000000000000 : ℝ)^16 ≤ (10263392825757491/10000000000000000 : ℝ)^83 := by
      have hnat : (114438409037251435061 : ℕ)^16*10000000000000000^83 ≤ 10263392825757491^83*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        114438409037251435061 100000000000000000000 10263392825757491 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10263392825757491/10000000000000000 : ℝ)) (X := (114438409037251435061/100000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (64438409037251435061/50000000000000000000 : ℝ) ≤ (10501190007160699/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (64438409037251435061/50000000000000000000 : ℝ)^16 ≤ (10501190007160699/10000000000000000 : ℝ)^83 := by
      have hnat : (64438409037251435061 : ℕ)^16*10000000000000000^83 ≤ 10501190007160699^83*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64438409037251435061 50000000000000000000 10501190007160699 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10501190007160699/10000000000000000 : ℝ)) (X := (64438409037251435061/50000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(263392825757491/6886200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1292375985887/37425000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (34431/50000 : ℝ)) (alpha := (263392825757491/6886200000000000 : ℝ)) (beta := (1292375985887/37425000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (34431/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(263392825757491/6886200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1292375985887/37425000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (29203/50000 : ℝ) ^ (83/16 : ℝ) ≤ (307233168268816299/5000000000000000000 : ℝ) := by
    have hpowers : (29203/50000 : ℝ)^83 ≤ (307233168268816299/5000000000000000000 : ℝ)^16 := by
      have hnat : (29203 : ℕ)^83*5000000000000000000^16 ≤ 307233168268816299^16*50000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29203 50000 307233168268816299 5000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29203/50000 : ℝ)) (X := (307233168268816299/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (5307233168268816299/5000000000000000000 : ℝ) ≤ (10115617921064193/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (5307233168268816299/5000000000000000000 : ℝ)^16 ≤ (10115617921064193/10000000000000000 : ℝ)^83 := by
      have hnat : (5307233168268816299 : ℕ)^16*10000000000000000^83 ≤ 10115617921064193^83*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5307233168268816299 5000000000000000000 10115617921064193 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10115617921064193/10000000000000000 : ℝ)) (X := (5307233168268816299/5000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (2807233168268816299/2500000000000000000 : ℝ) ≤ (10225953250806807/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2807233168268816299/2500000000000000000 : ℝ)^16 ≤ (10225953250806807/10000000000000000 : ℝ)^83 := by
      have hnat : (2807233168268816299 : ℕ)^16*10000000000000000^83 ≤ 10225953250806807^83*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2807233168268816299 2500000000000000000 10225953250806807 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10225953250806807/10000000000000000 : ℝ)) (X := (2807233168268816299/2500000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(115617921064193/5840600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(55167664871307/2920300000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (29203/50000 : ℝ)) (alpha := (115617921064193/5840600000000000 : ℝ)) (beta := (55167664871307/2920300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (29203/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(115617921064193/5840600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(55167664871307/2920300000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-737671011/5000000000 : ℝ)*X 0 0+(4961049663/10000000000 : ℝ)*X 0 1+(-5569356467/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323062_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2483176837/5000000000 : ℝ)*X 1 0+(-737401963/5000000000 : ℝ)*X 1 1+(-1112917473/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323062_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2544977671/5000000000 : ℝ)*X 2 0+(2548275651/5000000000 : ℝ)*X 2 1+(481959273/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323062_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2722391309/5000000000 : ℝ)*X 0 0+(2721290287/5000000000 : ℝ)*X 0 1+(-60970609/625000000 : ℝ)*X 0 2+(2722391309/5000000000 : ℝ)*X 1 0+(2721290287/5000000000 : ℝ)*X 1 1+(-60970609/625000000 : ℝ)*X 1 2+(2722391309/5000000000 : ℝ)*X 2 0+(2721290287/5000000000 : ℝ)*X 2 1+(-60970609/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323062_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-237182319/2000000000 : ℝ)*X 0 0+(2299408997/5000000000 : ℝ)*X 0 1+(-6119129661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323062_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((4976052769/10000000000 : ℝ)*X 1 0+(-97227159/1000000000 : ℝ)*X 1 1+(-2952081439/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323062_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1225411177/2500000000 : ℝ)*X 2 0+(2907915661/5000000000 : ℝ)*X 2 1+(1209697103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323062_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((5167485033/10000000000 : ℝ)*X 0 0+(238413827/400000000 : ℝ)*X 0 1+(-58332967/1000000000 : ℝ)*X 0 2+(5167485033/10000000000 : ℝ)*X 1 0+(238413827/400000000 : ℝ)*X 1 1+(-58332967/1000000000 : ℝ)*X 1 2+(5167485033/10000000000 : ℝ)*X 2 0+(238413827/400000000 : ℝ)*X 2 1+(-58332967/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323062_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-446087459/5000000000 : ℝ)*X 0 0+(97551731/200000000 : ℝ)*X 0 1+(-189061859/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323062_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4708821427/10000000000 : ℝ)*X 1 0+(-128445513/1000000000 : ℝ)*X 1 1+(-594779793/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323062_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((569149747/1000000000 : ℝ)*X 2 0+(1253367659/2500000000 : ℝ)*X 2 1+(308313421/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323062_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3117688819/5000000000 : ℝ)*X 0 0+(2438071491/5000000000 : ℝ)*X 0 1+(-589051523/10000000000 : ℝ)*X 0 2+(3117688819/5000000000 : ℝ)*X 1 0+(2438071491/5000000000 : ℝ)*X 1 1+(-589051523/10000000000 : ℝ)*X 1 2+(3117688819/5000000000 : ℝ)*X 2 0+(2438071491/5000000000 : ℝ)*X 2 1+(-589051523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323062_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-707325123/10000000000 : ℝ)*X 0 0+(1052877379/2000000000 : ℝ)*X 0 1+(-23169631/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323062_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((5752400071/10000000000 : ℝ)*X 1 0+(-594739817/5000000000 : ℝ)*X 1 1+(-4981958611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323062_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((954931907/2000000000 : ℝ)*X 2 0+(5400267773/10000000000 : ℝ)*X 2 1+(1936695723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323062_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((640463249/1000000000 : ℝ)*X 0 0+(4599499951/10000000000 : ℝ)*X 0 1+(-740714909/10000000000 : ℝ)*X 0 2+(640463249/1000000000 : ℝ)*X 1 0+(4599499951/10000000000 : ℝ)*X 1 1+(-740714909/10000000000 : ℝ)*X 1 2+(640463249/1000000000 : ℝ)*X 2 0+(4599499951/10000000000 : ℝ)*X 2 1+(-740714909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323062_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((33731/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33731/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4834201633669394861113612678117/290167220938250000000000000000000000 : ℝ) := by norm_num
    linear_combination (212752732279/500000000000 : ℝ)*(base39) + (46810778877/250000000000 : ℝ)*(base49) + (224699043899/1000000000000 : ℝ)*(base60) + (951078415601/125000000000 : ℝ)*(major_s1_0) + (951078415601/125000000000 : ℝ)*(major_s1_1) + (951078415601/125000000000 : ℝ)*(major_s1_2) + (460973/62500000000 : ℝ)*(sp_s1_0) + (273386999/1000000000000 : ℝ)*(sp_s1_1) + (5664013244897/500000000000 : ℝ)*(sp_s1_7) + (176995123137/15625000000 : ℝ)*(sp_s1_8) + (5663885724031/500000000000 : ℝ)*(sp_s1_9) + (1944607615447/500000000000 : ℝ)*(sp_s1_13) + (14519519/200000000000 : ℝ)*(sp_s1_15) + (262417301/1000000000000 : ℝ)*(sp_s1_23) + (1944607615447/500000000000 : ℝ)*(f.failure) + (5664016932681/500000000000 : ℝ)*(f.sum) + (3904085640491967509/6284303081250000000000000000000 : ℝ)*base63 + (39771137383989/730075000000000000000000000 : ℝ)*base65 + (12330530025829/37425000000000000000000000 : ℝ)*base66 + (1468858799412711/1460150000000000000000000000 : ℝ)*base69 + (8223217463817066357/25282497250000000000000000000000 : ℝ)*base70 + (581956958434099/865750000000000000000000000 : ℝ)*base72 + (68885682591067/1721550000000000000000000000 : ℝ)*base75 + (7161843139767/432875000000000000000000000 : ℝ)*base76 + (476935095974550673/1296027750000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (20801/25000000000000000 : ℝ)*base86 + (20801/25000000000000000 : ℝ)*base88 + (20801/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33983/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33983/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (494622007665519234612847341/106239714760000000000000000000000 : ℝ) := by norm_num
    linear_combination (192149977341/500000000000 : ℝ)*(base39) + (270722334249/1000000000000 : ℝ)*(base49) + (1124559/1000000000000 : ℝ)*(base59) + (7821602253117/1000000000000 : ℝ)*(major_s1_0) + (7821602253117/1000000000000 : ℝ)*(major_s1_1) + (7821602253117/1000000000000 : ℝ)*(major_s1_2) + (56615387/1000000000000 : ℝ)*(sp_s1_0) + (19591619/1000000000000 : ℝ)*(sp_s1_6) + (11644959805909/1000000000000 : ℝ)*(sp_s1_14) + (11645123758927/1000000000000 : ℝ)*(sp_s1_15) + (11645123758927/1000000000000 : ℝ)*(sp_s1_16) + (1998953750921/500000000000 : ℝ)*(sp_s1_20) + (107337631/1000000000000 : ℝ)*(sp_s1_21) + (76050967/500000000000 : ℝ)*(sp_s1_27) + (1999039597697/500000000000 : ℝ)*(f.failure) + (11645123758927/1000000000000 : ℝ)*(f.sum) + (333254176474127763/728614850000000000000000000000 : ℝ)*base62 + (2497795648755881/2920300000000000000000000000 : ℝ)*base64 + (16017663133291/24950000000000000000000000 : ℝ)*base67 + (6411379828362039/5840600000000000000000000000 : ℝ)*base68 + (43528211803440751119/202259978000000000000000000000000 : ℝ)*base70 + (2878398402515021/3463000000000000000000000000 : ℝ)*base73 + (113932633410277/99800000000000000000000000 : ℝ)*base74 + (7362553394964353/6926000000000000000000000000 : ℝ)*base76 + (90646447276199239/1728037000000000000000000000000 : ℝ)*base79 + (2449/25000000000000000 : ℝ)*base87 + (2449/25000000000000000 : ℝ)*base89 + (2449/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5309/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5309/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2044410846452761714534410006099/232133776750600000000000000000000000 : ℝ) := by norm_num
    linear_combination (1220781/250000000000 : ℝ)*(base11) + (916620733269/1000000000000 : ℝ)*(base39) + (430127/1000000000000 : ℝ)*(base40) + (18519554787/100000000000 : ℝ)*(base49) + (1219336712673/200000000000 : ℝ)*(major_s1_0) + (1219336712673/200000000000 : ℝ)*(major_s1_1) + (1219336712673/200000000000 : ℝ)*(major_s1_2) + (1788029/62500000000 : ℝ)*(sp_s1_0) + (18302357/1000000000000 : ℝ)*(sp_s1_2) + (63480899/1000000000000 : ℝ)*(sp_s1_9) + (9076958512947/1000000000000 : ℝ)*(sp_s1_21) + (1815398400907/200000000000 : ℝ)*(sp_s1_22) + (9076910221279/1000000000000 : ℝ)*(sp_s1_23) + (1558186093257/500000000000 : ℝ)*(sp_s1_27) + (1558186093257/500000000000 : ℝ)*(f.failure) + (1815398400907/200000000000 : ℝ)*(f.sum) + (159982720779453073/3351628310000000000000000000000 : ℝ)*base63 + (5030295739371/116812000000000000000000000 : ℝ)*base64 + (142883859947/499000000000000000000000 : ℝ)*base67 + (17531159379749/1168120000000000000000000000 : ℝ)*base69 + (1910792201750639051/40451995600000000000000000000000 : ℝ)*base70 + (175990748901491/692600000000000000000000000 : ℝ)*base72 + (20003301889893/459080000000000000000000000 : ℝ)*base75 + (160681236818317/1385200000000000000000000000 : ℝ)*base76 + (6131872869275011/345607400000000000000000000000 : ℝ)*base79 + (5031/25000000000000000 : ℝ)*base86 + (5031/25000000000000000 : ℝ)*base88 + (5031/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((3463/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3463/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34431/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34431/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-29203/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-29203/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((33731/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33731/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33983/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33983/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5309/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5309/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c323062_s1 p hpa hpb X hX hprev0

#print axioms solution

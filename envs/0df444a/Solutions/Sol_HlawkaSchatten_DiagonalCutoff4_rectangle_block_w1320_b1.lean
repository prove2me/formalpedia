-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1320_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:43:00.697993+00:00
-- url     : https://prove2.me/submissions/0485a352-782e-4777-8b29-84cda7f2c488

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
theorem support_rectangle_w1320_s3_0 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-515282581/2500000000 : ℝ)*x 0 + (543007967/1000000000 : ℝ)*x 1 + (2614491007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515282581/2500000000 : ℝ)^535 ≤ (6271394920923/50000000000000 : ℝ)^407 := by
    have hnat : (515282581 : ℕ)^535*50000000000000^407 ≤ 6271394920923^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515282581 2500000000 6271394920923 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543007967/1000000000 : ℝ)^535 ≤ (22406485074109/50000000000000 : ℝ)^407 := by
    have hnat : (543007967 : ℕ)^535*50000000000000^407 ≤ 22406485074109^407*1000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543007967 1000000000 22406485074109 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614491007/5000000000 : ℝ)^535 ≤ (10661059998641/25000000000000 : ℝ)^407 := by
    have hnat : (2614491007 : ℕ)^535*25000000000000^407 ≤ 10661059998641^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614491007 5000000000 10661059998641 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-515282581/2500000000 : ℝ), (543007967/1000000000 : ℝ), (2614491007/5000000000 : ℝ)] ![(6271394920923/50000000000000 : ℝ), (22406485074109/50000000000000 : ℝ), (10661059998641/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-515282581/2500000000 : ℝ)|^535 ≤ (6271394920923/50000000000000 : ℝ)^407
        have hw : |(-515282581/2500000000 : ℝ)|=(515282581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543007967/1000000000 : ℝ)|^535 ≤ (22406485074109/50000000000000 : ℝ)^407
        have hw : |(543007967/1000000000 : ℝ)|=(543007967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614491007/5000000000 : ℝ)|^535 ≤ (10661059998641/25000000000000 : ℝ)^407
        have hw : |(2614491007/5000000000 : ℝ)|=(2614491007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s3_1 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2676745987/5000000000 : ℝ)*x 0 + (-1081983011/5000000000 : ℝ)*x 1 + (2614491033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676745987/5000000000 : ℝ)^535 ≤ (43983981674779/100000000000000 : ℝ)^407 := by
    have hnat : (2676745987 : ℕ)^535*100000000000000^407 ≤ 43983981674779^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676745987 5000000000 43983981674779 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081983011/5000000000 : ℝ)^535 ≤ (6685888877169/50000000000000 : ℝ)^407 := by
    have hnat : (1081983011 : ℕ)^535*50000000000000^407 ≤ 6685888877169^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081983011 5000000000 6685888877169 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614491033/5000000000 : ℝ)^535 ≤ (21322120276007/50000000000000 : ℝ)^407 := by
    have hnat : (2614491033 : ℕ)^535*50000000000000^407 ≤ 21322120276007^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614491033 5000000000 21322120276007 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676745987/5000000000 : ℝ), (-1081983011/5000000000 : ℝ), (2614491033/5000000000 : ℝ)] ![(43983981674779/100000000000000 : ℝ), (6685888877169/50000000000000 : ℝ), (21322120276007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676745987/5000000000 : ℝ)|^535 ≤ (43983981674779/100000000000000 : ℝ)^407
        have hw : |(2676745987/5000000000 : ℝ)|=(2676745987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1081983011/5000000000 : ℝ)|^535 ≤ (6685888877169/50000000000000 : ℝ)^407
        have hw : |(-1081983011/5000000000 : ℝ)|=(1081983011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614491033/5000000000 : ℝ)|^535 ≤ (21322120276007/50000000000000 : ℝ)^407
        have hw : |(2614491033/5000000000 : ℝ)|=(2614491033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s3_2 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5353491821/10000000000 : ℝ)*x 0 + (163405699/312500000 : ℝ)*x 1 + (-2163965827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353491821/10000000000 : ℝ)^535 ≤ (21991990011203/50000000000000 : ℝ)^407 := by
    have hnat : (5353491821 : ℕ)^535*50000000000000^407 ≤ 21991990011203^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353491821 10000000000 21991990011203 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163405699/312500000 : ℝ)^535 ≤ (5330530473689/12500000000000 : ℝ)^407 := by
    have hnat : (163405699 : ℕ)^535*12500000000000^407 ≤ 5330530473689^407*312500000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163405699 312500000 5330530473689 12500000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2163965827/10000000000 : ℝ)^535 ≤ (668588808521/5000000000000 : ℝ)^407 := by
    have hnat : (2163965827 : ℕ)^535*5000000000000^407 ≤ 668588808521^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163965827 10000000000 668588808521 5000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353491821/10000000000 : ℝ), (163405699/312500000 : ℝ), (-2163965827/10000000000 : ℝ)] ![(21991990011203/50000000000000 : ℝ), (5330530473689/12500000000000 : ℝ), (668588808521/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353491821/10000000000 : ℝ)|^535 ≤ (21991990011203/50000000000000 : ℝ)^407
        have hw : |(5353491821/10000000000 : ℝ)|=(5353491821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163405699/312500000 : ℝ)|^535 ≤ (5330530473689/12500000000000 : ℝ)^407
        have hw : |(163405699/312500000 : ℝ)|=(163405699/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2163965827/10000000000 : ℝ)|^535 ≤ (668588808521/5000000000000 : ℝ)^407
        have hw : |(-2163965827/10000000000 : ℝ)|=(2163965827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s3_3 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4331197123/10000000000 : ℝ)*x 0 + (4127083081/10000000000 : ℝ)*x 1 + (568101553/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331197123/10000000000 : ℝ)^535 ≤ (33290666453677/100000000000000 : ℝ)^407 := by
    have hnat : (4331197123 : ℕ)^535*100000000000000^407 ≤ 33290666453677^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331197123 10000000000 33290666453677 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4127083081/10000000000 : ℝ)^535 ≤ (3124384094217/10000000000000 : ℝ)^407 := by
    have hnat : (4127083081 : ℕ)^535*10000000000000^407 ≤ 3124384094217^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127083081 10000000000 3124384094217 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568101553/1250000000 : ℝ)^535 ≤ (7093098517471/20000000000000 : ℝ)^407 := by
    have hnat : (568101553 : ℕ)^535*20000000000000^407 ≤ 7093098517471^407*1250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568101553 1250000000 7093098517471 20000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331197123/10000000000 : ℝ), (4127083081/10000000000 : ℝ), (568101553/1250000000 : ℝ)] ![(33290666453677/100000000000000 : ℝ), (3124384094217/10000000000000 : ℝ), (7093098517471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331197123/10000000000 : ℝ)|^535 ≤ (33290666453677/100000000000000 : ℝ)^407
        have hw : |(4331197123/10000000000 : ℝ)|=(4331197123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4127083081/10000000000 : ℝ)|^535 ≤ (3124384094217/10000000000000 : ℝ)^407
        have hw : |(4127083081/10000000000 : ℝ)|=(4127083081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(568101553/1250000000 : ℝ)|^535 ≤ (7093098517471/20000000000000 : ℝ)^407
        have hw : |(568101553/1250000000 : ℝ)|=(568101553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s3_4 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2061150919/10000000000 : ℝ)*x 0 + (653728951/1250000000 : ℝ)*x 1 + (542922487/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2061150919/10000000000 : ℝ)^535 ≤ (6271477293101/50000000000000 : ℝ)^407 := by
    have hnat : (2061150919 : ℕ)^535*50000000000000^407 ≤ 6271477293101^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061150919 10000000000 6271477293101 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653728951/1250000000 : ℝ)^535 ≤ (42653348038893/100000000000000 : ℝ)^407 := by
    have hnat : (653728951 : ℕ)^535*100000000000000^407 ≤ 42653348038893^407*1250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653728951 1250000000 42653348038893 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542922487/1000000000 : ℝ)^535 ≤ (11200924338281/25000000000000 : ℝ)^407 := by
    have hnat : (542922487 : ℕ)^535*25000000000000^407 ≤ 11200924338281^407*1000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542922487 1000000000 11200924338281 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2061150919/10000000000 : ℝ), (653728951/1250000000 : ℝ), (542922487/1000000000 : ℝ)] ![(6271477293101/50000000000000 : ℝ), (42653348038893/100000000000000 : ℝ), (11200924338281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2061150919/10000000000 : ℝ)|^535 ≤ (6271477293101/50000000000000 : ℝ)^407
        have hw : |(-2061150919/10000000000 : ℝ)|=(2061150919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653728951/1250000000 : ℝ)|^535 ≤ (42653348038893/100000000000000 : ℝ)^407
        have hw : |(653728951/1250000000 : ℝ)|=(653728951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542922487/1000000000 : ℝ)|^535 ≤ (11200924338281/25000000000000 : ℝ)^407
        have hw : |(542922487/1000000000 : ℝ)|=(542922487/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s3_5 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (530182549/1000000000 : ℝ)*x 0 + (-490930783/2500000000 : ℝ)*x 1 + (542922483/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530182549/1000000000 : ℝ)^535 ≤ (21713420658399/50000000000000 : ℝ)^407 := by
    have hnat : (530182549 : ℕ)^535*50000000000000^407 ≤ 21713420658399^407*1000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530182549 1000000000 21713420658399 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (490930783/2500000000 : ℝ)^535 ≤ (11769461751393/100000000000000 : ℝ)^407 := by
    have hnat : (490930783 : ℕ)^535*100000000000000^407 ≤ 11769461751393^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490930783 2500000000 11769461751393 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542922483/1000000000 : ℝ)^535 ≤ (44803696919219/100000000000000 : ℝ)^407 := by
    have hnat : (542922483 : ℕ)^535*100000000000000^407 ≤ 44803696919219^407*1000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542922483 1000000000 44803696919219 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530182549/1000000000 : ℝ), (-490930783/2500000000 : ℝ), (542922483/1000000000 : ℝ)] ![(21713420658399/50000000000000 : ℝ), (11769461751393/100000000000000 : ℝ), (44803696919219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530182549/1000000000 : ℝ)|^535 ≤ (21713420658399/50000000000000 : ℝ)^407
        have hw : |(530182549/1000000000 : ℝ)|=(530182549/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-490930783/2500000000 : ℝ)|^535 ≤ (11769461751393/100000000000000 : ℝ)^407
        have hw : |(-490930783/2500000000 : ℝ)|=(490930783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542922483/1000000000 : ℝ)|^535 ≤ (44803696919219/100000000000000 : ℝ)^407
        have hw : |(542922483/1000000000 : ℝ)|=(542922483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s3_6 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1325456409/2500000000 : ℝ)*x 0 + (5429224703/10000000000 : ℝ)*x 1 + (-1963723107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325456409/2500000000 : ℝ)^535 ≤ (43426842888771/100000000000000 : ℝ)^407 := by
    have hnat : (1325456409 : ℕ)^535*100000000000000^407 ≤ 43426842888771^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325456409 2500000000 43426842888771 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429224703/10000000000 : ℝ)^535 ≤ (700057742837/1562500000000 : ℝ)^407 := by
    have hnat : (5429224703 : ℕ)^535*1562500000000^407 ≤ 700057742837^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429224703 10000000000 700057742837 1562500000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1963723107/10000000000 : ℝ)^535 ≤ (5884730777217/50000000000000 : ℝ)^407 := by
    have hnat : (1963723107 : ℕ)^535*50000000000000^407 ≤ 5884730777217^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963723107 10000000000 5884730777217 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325456409/2500000000 : ℝ), (5429224703/10000000000 : ℝ), (-1963723107/10000000000 : ℝ)] ![(43426842888771/100000000000000 : ℝ), (700057742837/1562500000000 : ℝ), (5884730777217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325456409/2500000000 : ℝ)|^535 ≤ (43426842888771/100000000000000 : ℝ)^407
        have hw : |(1325456409/2500000000 : ℝ)|=(1325456409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429224703/10000000000 : ℝ)|^535 ≤ (700057742837/1562500000000 : ℝ)^407
        have hw : |(5429224703/10000000000 : ℝ)|=(5429224703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1963723107/10000000000 : ℝ)|^535 ≤ (5884730777217/50000000000000 : ℝ)^407
        have hw : |(-1963723107/10000000000 : ℝ)|=(1963723107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s3_7 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (866248009/2000000000 : ℝ)*x 0 + (4543047619/10000000000 : ℝ)*x 1 + (516107301/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866248009/2000000000 : ℝ)^535 ≤ (33291100118843/100000000000000 : ℝ)^407 := by
    have hnat : (866248009 : ℕ)^535*100000000000000^407 ≤ 33291100118843^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866248009 2000000000 33291100118843 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4543047619/10000000000 : ℝ)^535 ≤ (35447390877091/100000000000000 : ℝ)^407 := by
    have hnat : (4543047619 : ℕ)^535*100000000000000^407 ≤ 35447390877091^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543047619 10000000000 35447390877091 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516107301/1250000000 : ℝ)^535 ≤ (31261508979591/100000000000000 : ℝ)^407 := by
    have hnat : (516107301 : ℕ)^535*100000000000000^407 ≤ 31261508979591^407*1250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516107301 1250000000 31261508979591 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866248009/2000000000 : ℝ), (4543047619/10000000000 : ℝ), (516107301/1250000000 : ℝ)] ![(33291100118843/100000000000000 : ℝ), (35447390877091/100000000000000 : ℝ), (31261508979591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866248009/2000000000 : ℝ)|^535 ≤ (33291100118843/100000000000000 : ℝ)^407
        have hw : |(866248009/2000000000 : ℝ)|=(866248009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4543047619/10000000000 : ℝ)|^535 ≤ (35447390877091/100000000000000 : ℝ)^407
        have hw : |(4543047619/10000000000 : ℝ)|=(4543047619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516107301/1250000000 : ℝ)|^535 ≤ (31261508979591/100000000000000 : ℝ)^407
        have hw : |(516107301/1250000000 : ℝ)|=(516107301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1320_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1213/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10777/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1879/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8097/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1213/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8097/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1213/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8097/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1213/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8097/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1213/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8097/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1213/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8097/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1213/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1213/12500 : ℝ) ^ (4279/1024 : ℝ) ≤ (1461168111703099/25000000000000000000 : ℝ) := by
    have hpowers : (1213/12500 : ℝ)^4279 ≤ (1461168111703099/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1213 : ℕ)^4279*25000000000000000000^1024 ≤ 1461168111703099^1024*12500^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1213 12500 1461168111703099 25000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1213/12500 : ℝ)) (X := (1461168111703099/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8097/50000 : ℝ) ^ (4279/1024 : ℝ) ≤ (24836447729512793/50000000000000000000 : ℝ) := by
    have hpowers : (8097/50000 : ℝ)^4279 ≤ (24836447729512793/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8097 : ℕ)^4279*50000000000000000000^1024 ≤ 24836447729512793^1024*50000^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8097 50000 24836447729512793 50000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8097/50000 : ℝ)) (X := (24836447729512793/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501461168111703099/12500000000000000000 : ℝ) ≤ (5000139861615179/5000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (12501461168111703099/12500000000000000000 : ℝ)^1024 ≤ (5000139861615179/5000000000000000 : ℝ)^4279 := by
      have hnat : (12501461168111703099 : ℕ)^1024*5000000000000000^4279 ≤ 5000139861615179^4279*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501461168111703099 12500000000000000000 5000139861615179 5000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000139861615179/5000000000000000 : ℝ)) (X := (12501461168111703099/12500000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50027758783952918991/50000000000000000000 : ℝ) ≤ (20002656601499/20000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (50027758783952918991/50000000000000000000 : ℝ)^1024 ≤ (20002656601499/20000000000000 : ℝ)^4279 := by
      have hnat : (50027758783952918991 : ℕ)^1024*20000000000000^4279 ≤ 20002656601499^4279*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027758783952918991 50000000000000000000 20002656601499 20000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20002656601499/20000000000000 : ℝ)) (X := (50027758783952918991/50000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25024836447729512793/25000000000000000000 : ℝ) ≤ (5001188439134321/5000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (25024836447729512793/25000000000000000000 : ℝ)^1024 ≤ (5001188439134321/5000000000000000 : ℝ)^4279 := by
      have hnat : (25024836447729512793 : ℕ)^1024*5000000000000000^4279 ≤ 5001188439134321^4279*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25024836447729512793 25000000000000000000 5001188439134321 5000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001188439134321/5000000000000000 : ℝ)) (X := (25024836447729512793/25000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1461168111703099/25000000000000000000 : ℝ) ≤ ((16220366152818378871/16225000000000000000 : ℝ)+2*(524288759571/324500000000000 : ℝ)*(1213/12500 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (16220366152818378871/16225000000000000000 : ℝ)+2*(524288759571/324500000000000 : ℝ)*(1213/12500 : ℝ)=(5000139861615179/5000000000000000 : ℝ) by norm_num, show 1+2*(1461168111703099/25000000000000000000 : ℝ)=(12501461168111703099/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24836447729512793/50000000000000000000 : ℝ)+(1461168111703099/25000000000000000000 : ℝ) ≤ ((16220366152818378871/16225000000000000000 : ℝ)+(524288759571/324500000000000 : ℝ)*((8097/50000 : ℝ)+(1213/12500 : ℝ)))^(4279/1024 : ℝ) := by
    rw [show (16220366152818378871/16225000000000000000 : ℝ)+(524288759571/324500000000000 : ℝ)*((8097/50000 : ℝ)+(1213/12500 : ℝ))=(20002656601499/20000000000000 : ℝ) by norm_num, show 1+(24836447729512793/50000000000000000000 : ℝ)+(1461168111703099/25000000000000000000 : ℝ)=(50027758783952918991/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24836447729512793/50000000000000000000 : ℝ) ≤ ((16220366152818378871/16225000000000000000 : ℝ)+2*(524288759571/324500000000000 : ℝ)*(8097/50000 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (16220366152818378871/16225000000000000000 : ℝ)+2*(524288759571/324500000000000 : ℝ)*(8097/50000 : ℝ)=(5001188439134321/5000000000000000 : ℝ) by norm_num, show 1+2*(24836447729512793/50000000000000000000 : ℝ)=(25024836447729512793/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16220366152818378871/16225000000000000000 : ℝ)*(X 1 0+X 2 0)+(524288759571/324500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (1213/12500 : ℝ)) (hi := (8097/50000 : ℝ)) (c := (16220366152818378871/16225000000000000000 : ℝ)) (alpha := (524288759571/324500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16220366152818378871/16225000000000000000 : ℝ)*(X 0 1+X 2 1)+(524288759571/324500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (1213/12500 : ℝ)) (hi := (8097/50000 : ℝ)) (c := (16220366152818378871/16225000000000000000 : ℝ)) (alpha := (524288759571/324500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16220366152818378871/16225000000000000000 : ℝ)*(X 0 2+X 1 2)+(524288759571/324500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (1213/12500 : ℝ)) (hi := (8097/50000 : ℝ)) (c := (16220366152818378871/16225000000000000000 : ℝ)) (alpha := (524288759571/324500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-515282581/2500000000 : ℝ)*X 0 0+(543007967/1000000000 : ℝ)*X 0 1+(2614491007/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676745987/5000000000 : ℝ)*X 1 0+(-1081983011/5000000000 : ℝ)*X 1 1+(2614491033/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353491821/10000000000 : ℝ)*X 2 0+(163405699/312500000 : ℝ)*X 2 1+(-2163965827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4331197123/10000000000 : ℝ)*X 0 0+(4127083081/10000000000 : ℝ)*X 0 1+(568101553/1250000000 : ℝ)*X 0 2+(4331197123/10000000000 : ℝ)*X 1 0+(4127083081/10000000000 : ℝ)*X 1 1+(568101553/1250000000 : ℝ)*X 1 2+(4331197123/10000000000 : ℝ)*X 2 0+(4127083081/10000000000 : ℝ)*X 2 1+(568101553/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2061150919/10000000000 : ℝ)*X 0 0+(653728951/1250000000 : ℝ)*X 0 1+(542922487/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530182549/1000000000 : ℝ)*X 1 0+(-490930783/2500000000 : ℝ)*X 1 1+(542922483/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325456409/2500000000 : ℝ)*X 2 0+(5429224703/10000000000 : ℝ)*X 2 1+(-1963723107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((866248009/2000000000 : ℝ)*X 0 0+(4543047619/10000000000 : ℝ)*X 0 1+(516107301/1250000000 : ℝ)*X 0 2+(866248009/2000000000 : ℝ)*X 1 0+(4543047619/10000000000 : ℝ)*X 1 1+(516107301/1250000000 : ℝ)*X 1 2+(866248009/2000000000 : ℝ)*X 2 0+(4543047619/10000000000 : ℝ)*X 2 1+(516107301/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (373209136374746777658135147/36875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (840302499/50000000000000 : ℝ)*(base19) + (301048241/20000000000000 : ℝ)*(base23) + (55617/312500000000 : ℝ)*(lower2) + (121066671/100000000000000 : ℝ)*(upper3) + (272916621/100000000000000 : ℝ)*(upper5) + (1841674804168903/50000000000000 : ℝ)*(major0) + (1841674804168903/50000000000000 : ℝ)*(major1) + (1841674804168903/50000000000000 : ℝ)*(major2) + (4972739129033047/100000000000000 : ℝ)*(sp0) + (4972772736149573/100000000000000 : ℝ)*(sp1) + (2486386455756683/50000000000000 : ℝ)*(sp2) + (2393910561381813/100000000000000 : ℝ)*(sp3) + (8821930381/25000000000000 : ℝ)*(sp4) + (556047001/4000000000000 : ℝ)*(sp7) + (1196962231278419/50000000000000 : ℝ)*(f.failure) + (4972774416754571/100000000000000 : ℝ)*(f.sum) + (3208495082967/737500000000000000000000000 : ℝ)*base66 + (1045588189559218317/73750000000000000000000000000000 : ℝ)*base68 + (1152726071259218317/73750000000000000000000000000000 : ℝ)*base70 + (848861599739218317/73750000000000000000000000000000 : ℝ)*base72 + (863817559923/184375000000000000000000000 : ℝ)*base74 + (1551037968159218317/73750000000000000000000000000000 : ℝ)*base76 + (1062305338059218317/73750000000000000000000000000000 : ℝ)*base78 + (988088678001718317/73750000000000000000000000000000 : ℝ)*base80 + (1190384257171/368750000000000000000000000 : ℝ)*base82 + (84267181/5000000000000000000000 : ℝ)*base89 + (84267181/5000000000000000000000 : ℝ)*base91 + (84267181/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (882206374154725537416973059/202812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1094309277/100000000000000 : ℝ)*(base19) + (1268180483/100000000000000 : ℝ)*(base23) + (11357131/10000000000000 : ℝ)*(upper3) + (1178079/10000000000000 : ℝ)*(lower4) + (120319281/100000000000000 : ℝ)*(upper5) + (928696435917557/25000000000000 : ℝ)*(major0) + (928696435917557/25000000000000 : ℝ)*(major1) + (928696435917557/25000000000000 : ℝ)*(major2) + (2288172547/12500000000000 : ℝ)*(sp1) + (9847642569/50000000000000 : ℝ)*(sp2) + (1003043109847569/20000000000000 : ℝ)*(sp4) + (156724879673381/3125000000000 : ℝ)*(sp5) + (78362415402691/1562500000000 : ℝ)*(sp6) + (2414355793107209/100000000000000 : ℝ)*(sp7) + (2414355793107209/100000000000000 : ℝ)*(f.failure) + (1003043109847569/20000000000000 : ℝ)*(f.sum) + (11990348594531/8112500000000000000000000000 : ℝ)*base66 + (596560135662213147/405625000000000000000000000000000 : ℝ)*base67 + (1745063621124661853/405625000000000000000000000000000 : ℝ)*base70 + (914437842539036853/405625000000000000000000000000000 : ℝ)*base72 + (1934377327313/16225000000000000000000000000 : ℝ)*base73 + (3495149361454088147/405625000000000000000000000000000 : ℝ)*base75 + (568659205434713147/405625000000000000000000000000000 : ℝ)*base77 + (5417132772597213147/405625000000000000000000000000000 : ℝ)*base79 + (30948038767931/8112500000000000000000000000 : ℝ)*base82 + (40934391/10000000000000000000000 : ℝ)*base89 + (40934391/10000000000000000000000 : ℝ)*base91 + (40934391/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1320_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1213/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10777/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1879/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1320_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1320_s4_0 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1031389877/5000000000 : ℝ)*x 0 + (67710411/125000000 : ℝ)*x 1 + (81892913/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031389877/5000000000 : ℝ)^535 ≤ (2511197133643/20000000000000 : ℝ)^407 := by
    have hnat : (1031389877 : ℕ)^535*20000000000000^407 ≤ 2511197133643^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031389877 5000000000 2511197133643 20000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67710411/125000000 : ℝ)^535 ≤ (22334660868427/50000000000000 : ℝ)^407 := by
    have hnat : (67710411 : ℕ)^535*50000000000000^407 ≤ 22334660868427^407*125000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67710411 125000000 22334660868427 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81892913/156250000 : ℝ)^535 ≤ (5346836572703/12500000000000 : ℝ)^407 := by
    have hnat : (81892913 : ℕ)^535*12500000000000^407 ≤ 5346836572703^407*156250000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81892913 156250000 5346836572703 12500000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1031389877/5000000000 : ℝ), (67710411/125000000 : ℝ), (81892913/156250000 : ℝ)] ![(2511197133643/20000000000000 : ℝ), (22334660868427/50000000000000 : ℝ), (5346836572703/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1031389877/5000000000 : ℝ)|^535 ≤ (2511197133643/20000000000000 : ℝ)^407
        have hw : |(-1031389877/5000000000 : ℝ)|=(1031389877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67710411/125000000 : ℝ)|^535 ≤ (22334660868427/50000000000000 : ℝ)^407
        have hw : |(67710411/125000000 : ℝ)|=(67710411/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81892913/156250000 : ℝ)|^535 ≤ (5346836572703/12500000000000 : ℝ)^407
        have hw : |(81892913/156250000 : ℝ)|=(81892913/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s4_1 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (668765977/1250000000 : ℝ)*x 0 + (-1076184403/5000000000 : ℝ)*x 1 + (327571637/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668765977/1250000000 : ℝ)^535 ≤ (21973826472227/50000000000000 : ℝ)^407 := by
    have hnat : (668765977 : ℕ)^535*50000000000000^407 ≤ 21973826472227^407*1250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668765977 1250000000 21973826472227 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076184403/5000000000 : ℝ)^535 ≤ (6638828517893/50000000000000 : ℝ)^407 := by
    have hnat : (1076184403 : ℕ)^535*50000000000000^407 ≤ 6638828517893^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076184403 5000000000 6638828517893 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327571637/625000000 : ℝ)^535 ≤ (42774690006897/100000000000000 : ℝ)^407 := by
    have hnat : (327571637 : ℕ)^535*100000000000000^407 ≤ 42774690006897^407*625000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327571637 625000000 42774690006897 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668765977/1250000000 : ℝ), (-1076184403/5000000000 : ℝ), (327571637/625000000 : ℝ)] ![(21973826472227/50000000000000 : ℝ), (6638828517893/50000000000000 : ℝ), (42774690006897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668765977/1250000000 : ℝ)|^535 ≤ (21973826472227/50000000000000 : ℝ)^407
        have hw : |(668765977/1250000000 : ℝ)|=(668765977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1076184403/5000000000 : ℝ)|^535 ≤ (6638828517893/50000000000000 : ℝ)^407
        have hw : |(-1076184403/5000000000 : ℝ)|=(1076184403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327571637/625000000 : ℝ)|^535 ≤ (42774690006897/100000000000000 : ℝ)^407
        have hw : |(327571637/625000000 : ℝ)|=(327571637/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s4_2 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5350127777/10000000000 : ℝ)*x 0 + (524114591/1000000000 : ℝ)*x 1 + (-2152369231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350127777/10000000000 : ℝ)^535 ≤ (2746728282709/6250000000000 : ℝ)^407 := by
    have hnat : (5350127777 : ℕ)^535*6250000000000^407 ≤ 2746728282709^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350127777 10000000000 2746728282709 6250000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524114591/1000000000 : ℝ)^535 ≤ (42774686981593/100000000000000 : ℝ)^407 := by
    have hnat : (524114591 : ℕ)^535*100000000000000^407 ≤ 42774686981593^407*1000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524114591 1000000000 42774686981593 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2152369231/10000000000 : ℝ)^535 ≤ (6638830241043/50000000000000 : ℝ)^407 := by
    have hnat : (2152369231 : ℕ)^535*50000000000000^407 ≤ 6638830241043^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152369231 10000000000 6638830241043 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350127777/10000000000 : ℝ), (524114591/1000000000 : ℝ), (-2152369231/10000000000 : ℝ)] ![(2746728282709/6250000000000 : ℝ), (42774686981593/100000000000000 : ℝ), (6638830241043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350127777/10000000000 : ℝ)|^535 ≤ (2746728282709/6250000000000 : ℝ)^407
        have hw : |(5350127777/10000000000 : ℝ)|=(5350127777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524114591/1000000000 : ℝ)|^535 ≤ (42774686981593/100000000000000 : ℝ)^407
        have hw : |(524114591/1000000000 : ℝ)|=(524114591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2152369231/10000000000 : ℝ)|^535 ≤ (6638830241043/50000000000000 : ℝ)^407
        have hw : |(-2152369231/10000000000 : ℝ)|=(2152369231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s4_3 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (21660981/50000000 : ℝ)*x 0 + (519168801/1250000000 : ℝ)*x 1 + (2259147851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21660981/50000000 : ℝ)^535 ≤ (33300761042301/100000000000000 : ℝ)^407 := by
    have hnat : (21660981 : ℕ)^535*100000000000000^407 ≤ 33300761042301^407*50000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21660981 50000000 33300761042301 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (519168801/1250000000 : ℝ)^535 ≤ (15752748340879/50000000000000 : ℝ)^407 := by
    have hnat : (519168801 : ℕ)^535*50000000000000^407 ≤ 15752748340879^407*1250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519168801 1250000000 15752748340879 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259147851/5000000000 : ℝ)^535 ≤ (35193742260429/100000000000000 : ℝ)^407 := by
    have hnat : (2259147851 : ℕ)^535*100000000000000^407 ≤ 35193742260429^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259147851 5000000000 35193742260429 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21660981/50000000 : ℝ), (519168801/1250000000 : ℝ), (2259147851/5000000000 : ℝ)] ![(33300761042301/100000000000000 : ℝ), (15752748340879/50000000000000 : ℝ), (35193742260429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21660981/50000000 : ℝ)|^535 ≤ (33300761042301/100000000000000 : ℝ)^407
        have hw : |(21660981/50000000 : ℝ)|=(21660981/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(519168801/1250000000 : ℝ)|^535 ≤ (15752748340879/50000000000000 : ℝ)^407
        have hw : |(519168801/1250000000 : ℝ)|=(519168801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259147851/5000000000 : ℝ)|^535 ≤ (35193742260429/100000000000000 : ℝ)^407
        have hw : |(2259147851/5000000000 : ℝ)|=(2259147851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s4_4 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2062793483/10000000000 : ℝ)*x 0 + (524179523/1000000000 : ℝ)*x 1 + (677022577/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2062793483/10000000000 : ℝ)^535 ≤ (12556095517361/100000000000000 : ℝ)^407 := by
    have hnat : (2062793483 : ℕ)^535*100000000000000^407 ≤ 12556095517361^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062793483 10000000000 12556095517361 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524179523/1000000000 : ℝ)^535 ≤ (21390826520733/50000000000000 : ℝ)^407 := by
    have hnat : (524179523 : ℕ)^535*50000000000000^407 ≤ 21390826520733^407*1000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524179523 1000000000 21390826520733 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677022577/1250000000 : ℝ)^535 ≤ (44662251426467/100000000000000 : ℝ)^407 := by
    have hnat : (677022577 : ℕ)^535*100000000000000^407 ≤ 44662251426467^407*1250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677022577 1250000000 44662251426467 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2062793483/10000000000 : ℝ), (524179523/1000000000 : ℝ), (677022577/1250000000 : ℝ)] ![(12556095517361/100000000000000 : ℝ), (21390826520733/50000000000000 : ℝ), (44662251426467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2062793483/10000000000 : ℝ)|^535 ≤ (12556095517361/100000000000000 : ℝ)^407
        have hw : |(-2062793483/10000000000 : ℝ)|=(2062793483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524179523/1000000000 : ℝ)|^535 ≤ (21390826520733/50000000000000 : ℝ)^407
        have hw : |(524179523/1000000000 : ℝ)|=(524179523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677022577/1250000000 : ℝ)|^535 ≤ (44662251426467/100000000000000 : ℝ)^407
        have hw : |(677022577/1250000000 : ℝ)|=(677022577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s4_5 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5304991529/10000000000 : ℝ)*x 0 + (-988667369/5000000000 : ℝ)*x 1 + (541618061/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304991529/10000000000 : ℝ)^535 ≤ (21730466530449/50000000000000 : ℝ)^407 := by
    have hnat : (5304991529 : ℕ)^535*50000000000000^407 ≤ 21730466530449^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304991529 10000000000 21730466530449 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (988667369/5000000000 : ℝ)^535 ≤ (371150486213/3125000000000 : ℝ)^407 := by
    have hnat : (988667369 : ℕ)^535*3125000000000^407 ≤ 371150486213^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988667369 5000000000 371150486213 3125000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541618061/1000000000 : ℝ)^535 ≤ (4466225136143/10000000000000 : ℝ)^407 := by
    have hnat : (541618061 : ℕ)^535*10000000000000^407 ≤ 4466225136143^407*1000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541618061 1000000000 4466225136143 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304991529/10000000000 : ℝ), (-988667369/5000000000 : ℝ), (541618061/1000000000 : ℝ)] ![(21730466530449/50000000000000 : ℝ), (371150486213/3125000000000 : ℝ), (4466225136143/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304991529/10000000000 : ℝ)|^535 ≤ (21730466530449/50000000000000 : ℝ)^407
        have hw : |(5304991529/10000000000 : ℝ)|=(5304991529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-988667369/5000000000 : ℝ)|^535 ≤ (371150486213/3125000000000 : ℝ)^407
        have hw : |(-988667369/5000000000 : ℝ)|=(988667369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541618061/1000000000 : ℝ)|^535 ≤ (4466225136143/10000000000000 : ℝ)^407
        have hw : |(541618061/1000000000 : ℝ)|=(541618061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s4_6 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5304991541/10000000000 : ℝ)*x 0 + (1083236119/2000000000 : ℝ)*x 1 + (-988667371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304991541/10000000000 : ℝ)^535 ≤ (21730466595063/50000000000000 : ℝ)^407 := by
    have hnat : (5304991541 : ℕ)^535*50000000000000^407 ≤ 21730466595063^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304991541 10000000000 21730466595063 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083236119/2000000000 : ℝ)^535 ≤ (22331125599419/50000000000000 : ℝ)^407 := by
    have hnat : (1083236119 : ℕ)^535*50000000000000^407 ≤ 22331125599419^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083236119 2000000000 22331125599419 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (988667371/5000000000 : ℝ)^535 ≤ (5938407795199/50000000000000 : ℝ)^407 := by
    have hnat : (988667371 : ℕ)^535*50000000000000^407 ≤ 5938407795199^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988667371 5000000000 5938407795199 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304991541/10000000000 : ℝ), (1083236119/2000000000 : ℝ), (-988667371/5000000000 : ℝ)] ![(21730466595063/50000000000000 : ℝ), (22331125599419/50000000000000 : ℝ), (5938407795199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304991541/10000000000 : ℝ)|^535 ≤ (21730466595063/50000000000000 : ℝ)^407
        have hw : |(5304991541/10000000000 : ℝ)|=(5304991541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083236119/2000000000 : ℝ)|^535 ≤ (22331125599419/50000000000000 : ℝ)^407
        have hw : |(1083236119/2000000000 : ℝ)|=(1083236119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-988667371/5000000000 : ℝ)|^535 ≤ (5938407795199/50000000000000 : ℝ)^407
        have hw : |(-988667371/5000000000 : ℝ)|=(988667371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s4_7 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2166112393/5000000000 : ℝ)*x 0 + (1129236857/2500000000 : ℝ)*x 1 + (4154705769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166112393/5000000000 : ℝ)^535 ≤ (4162631235447/12500000000000 : ℝ)^407 := by
    have hnat : (2166112393 : ℕ)^535*12500000000000^407 ≤ 4162631235447^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166112393 5000000000 4162631235447 12500000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129236857/2500000000 : ℝ)^535 ≤ (35179938165057/100000000000000 : ℝ)^407 := by
    have hnat : (1129236857 : ℕ)^535*100000000000000^407 ≤ 35179938165057^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129236857 2500000000 35179938165057 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4154705769/10000000000 : ℝ)^535 ≤ (15759505970783/50000000000000 : ℝ)^407 := by
    have hnat : (4154705769 : ℕ)^535*50000000000000^407 ≤ 15759505970783^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154705769 10000000000 15759505970783 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166112393/5000000000 : ℝ), (1129236857/2500000000 : ℝ), (4154705769/10000000000 : ℝ)] ![(4162631235447/12500000000000 : ℝ), (35179938165057/100000000000000 : ℝ), (15759505970783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166112393/5000000000 : ℝ)|^535 ≤ (4162631235447/12500000000000 : ℝ)^407
        have hw : |(2166112393/5000000000 : ℝ)|=(2166112393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1129236857/2500000000 : ℝ)|^535 ≤ (35179938165057/100000000000000 : ℝ)^407
        have hw : |(1129236857/2500000000 : ℝ)|=(1129236857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4154705769/10000000000 : ℝ)|^535 ≤ (15759505970783/50000000000000 : ℝ)^407
        have hw : |(4154705769/10000000000 : ℝ)|=(4154705769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1320_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1879/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10777/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11037/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3689/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1879/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10777/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1879/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10777/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1879/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10777/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1879/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10777/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1879/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10777/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1879/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10777/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10777/100000 : ℝ) ^ (4279/1024 : ℝ) ≤ (9059168154896523/100000000000000000000 : ℝ) := by
    have hpowers : (10777/100000 : ℝ)^4279 ≤ (9059168154896523/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10777 : ℕ)^4279*100000000000000000000^1024 ≤ 9059168154896523^1024*100000^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10777 100000 9059168154896523 100000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10777/100000 : ℝ)) (X := (9059168154896523/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1879/12500 : ℝ) ^ (4279/1024 : ℝ) ≤ (1819537319601901/5000000000000000000 : ℝ) := by
    have hpowers : (1879/12500 : ℝ)^4279 ≤ (1819537319601901/5000000000000000000 : ℝ)^1024 := by
      have hnat : (1879 : ℕ)^4279*5000000000000000000^1024 ≤ 1819537319601901^1024*12500^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1879 12500 1819537319601901 5000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1879/12500 : ℝ)) (X := (1819537319601901/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009059168154896523/50000000000000000000 : ℝ) ≤ (10000433556858479/10000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (50009059168154896523/50000000000000000000 : ℝ)^1024 ≤ (10000433556858479/10000000000000000 : ℝ)^4279 := by
      have hnat : (50009059168154896523 : ℕ)^1024*10000000000000000^4279 ≤ 10000433556858479^4279*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009059168154896523 50000000000000000000 10000433556858479 10000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000433556858479/10000000000000000 : ℝ)) (X := (50009059168154896523/50000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045449914546934543/100000000000000000000 : ℝ) ≤ (10001087465980227/10000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (100045449914546934543/100000000000000000000 : ℝ)^1024 ≤ (10001087465980227/10000000000000000 : ℝ)^4279 := by
      have hnat : (100045449914546934543 : ℕ)^1024*10000000000000000^4279 ≤ 10001087465980227^4279*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045449914546934543 100000000000000000000 10001087465980227 10000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001087465980227/10000000000000000 : ℝ)) (X := (100045449914546934543/100000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501819537319601901/2500000000000000000 : ℝ) ≤ (400069655004079/400000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (2501819537319601901/2500000000000000000 : ℝ)^1024 ≤ (400069655004079/400000000000000 : ℝ)^4279 := by
      have hnat : (2501819537319601901 : ℕ)^1024*400000000000000^4279 ≤ 400069655004079^4279*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501819537319601901 2500000000000000000 400069655004079 400000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400069655004079/400000000000000 : ℝ)) (X := (2501819537319601901/2500000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9059168154896523/100000000000000000000 : ℝ) ≤ ((42537750427222671753/42550000000000000000 : ℝ)+2*(163477280437/106375000000000 : ℝ)*(10777/100000 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (42537750427222671753/42550000000000000000 : ℝ)+2*(163477280437/106375000000000 : ℝ)*(10777/100000 : ℝ)=(10000433556858479/10000000000000000 : ℝ) by norm_num, show 1+2*(9059168154896523/100000000000000000000 : ℝ)=(50009059168154896523/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1819537319601901/5000000000000000000 : ℝ)+(9059168154896523/100000000000000000000 : ℝ) ≤ ((42537750427222671753/42550000000000000000 : ℝ)+(163477280437/106375000000000 : ℝ)*((1879/12500 : ℝ)+(10777/100000 : ℝ)))^(4279/1024 : ℝ) := by
    rw [show (42537750427222671753/42550000000000000000 : ℝ)+(163477280437/106375000000000 : ℝ)*((1879/12500 : ℝ)+(10777/100000 : ℝ))=(10001087465980227/10000000000000000 : ℝ) by norm_num, show 1+(1819537319601901/5000000000000000000 : ℝ)+(9059168154896523/100000000000000000000 : ℝ)=(100045449914546934543/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1819537319601901/5000000000000000000 : ℝ) ≤ ((42537750427222671753/42550000000000000000 : ℝ)+2*(163477280437/106375000000000 : ℝ)*(1879/12500 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (42537750427222671753/42550000000000000000 : ℝ)+2*(163477280437/106375000000000 : ℝ)*(1879/12500 : ℝ)=(400069655004079/400000000000000 : ℝ) by norm_num, show 1+2*(1819537319601901/5000000000000000000 : ℝ)=(2501819537319601901/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (42537750427222671753/42550000000000000000 : ℝ)*(X 1 0+X 2 0)+(163477280437/106375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (10777/100000 : ℝ)) (hi := (1879/12500 : ℝ)) (c := (42537750427222671753/42550000000000000000 : ℝ)) (alpha := (163477280437/106375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (42537750427222671753/42550000000000000000 : ℝ)*(X 0 1+X 2 1)+(163477280437/106375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (10777/100000 : ℝ)) (hi := (1879/12500 : ℝ)) (c := (42537750427222671753/42550000000000000000 : ℝ)) (alpha := (163477280437/106375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (42537750427222671753/42550000000000000000 : ℝ)*(X 0 2+X 1 2)+(163477280437/106375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (10777/100000 : ℝ)) (hi := (1879/12500 : ℝ)) (c := (42537750427222671753/42550000000000000000 : ℝ)) (alpha := (163477280437/106375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1031389877/5000000000 : ℝ)*X 0 0+(67710411/125000000 : ℝ)*X 0 1+(81892913/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668765977/1250000000 : ℝ)*X 1 0+(-1076184403/5000000000 : ℝ)*X 1 1+(327571637/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350127777/10000000000 : ℝ)*X 2 0+(524114591/1000000000 : ℝ)*X 2 1+(-2152369231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((21660981/50000000 : ℝ)*X 0 0+(519168801/1250000000 : ℝ)*X 0 1+(2259147851/5000000000 : ℝ)*X 0 2+(21660981/50000000 : ℝ)*X 1 0+(519168801/1250000000 : ℝ)*X 1 1+(2259147851/5000000000 : ℝ)*X 1 2+(21660981/50000000 : ℝ)*X 2 0+(519168801/1250000000 : ℝ)*X 2 1+(2259147851/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2062793483/10000000000 : ℝ)*X 0 0+(524179523/1000000000 : ℝ)*X 0 1+(677022577/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304991529/10000000000 : ℝ)*X 1 0+(-988667369/5000000000 : ℝ)*X 1 1+(541618061/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304991541/10000000000 : ℝ)*X 2 0+(1083236119/2000000000 : ℝ)*X 2 1+(-988667371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2166112393/5000000000 : ℝ)*X 0 0+(1129236857/2500000000 : ℝ)*X 0 1+(4154705769/10000000000 : ℝ)*X 0 2+(2166112393/5000000000 : ℝ)*X 1 0+(1129236857/2500000000 : ℝ)*X 1 1+(4154705769/10000000000 : ℝ)*X 1 2+(2166112393/5000000000 : ℝ)*X 2 0+(1129236857/2500000000 : ℝ)*X 2 1+(4154705769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (463866265422369913821/71875000000000000000000000 : ℝ) := by norm_num
    linear_combination (1752295743/100000000000000 : ℝ)*(base19) + (339290787/20000000000000 : ℝ)*(base23) + (237616673/100000000000000 : ℝ)*(upper3) + (5870047/25000000000000 : ℝ)*(lower4) + (4216097494389539/100000000000000 : ℝ)*(major0) + (4216097494389539/100000000000000 : ℝ)*(major1) + (4216097494389539/100000000000000 : ℝ)*(major2) + (355749655332729/6250000000000 : ℝ)*(sp0) + (5692018994569843/100000000000000 : ℝ)*(sp1) + (2846006073722427/50000000000000 : ℝ)*(sp2) + (2740153865615821/100000000000000 : ℝ)*(sp3) + (13130770961/50000000000000 : ℝ)*(sp4) + (1725741699/25000000000000 : ℝ)*(sp6) + (10080585641/50000000000000 : ℝ)*(sp7) + (2740174026787103/100000000000000 : ℝ)*(f.failure) + (1138404149373117/20000000000000 : ℝ)*(f.sum) + (697539331553/287500000000000000000000000 : ℝ)*base65 + (3612862391589409/115000000000000000000000000000000 : ℝ)*base68 + (410357047331589409/115000000000000000000000000000000 : ℝ)*base70 + (1018776617568410591/115000000000000000000000000000000 : ℝ)*base71 + (153106277547/287500000000000000000000000 : ℝ)*base74 + (315014808771589409/115000000000000000000000000000000 : ℝ)*base76 + (609844747378410591/115000000000000000000000000000000 : ℝ)*base77 + (900831503908410591/115000000000000000000000000000000 : ℝ)*base79 + (1748864415347/287500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (29840097/10000000000000000000000 : ℝ)*base89 + (29840097/10000000000000000000000 : ℝ)*base91 + (29840097/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11741880889005049676322646317/1063750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78176939/4000000000000 : ℝ)*(base19) + (425387829/20000000000000 : ℝ)*(base23) + (225220507/100000000000000 : ℝ)*(upper3) + (73448951/100000000000000 : ℝ)*(lower4) + (117078877/50000000000000 : ℝ)*(upper5) + (2123753075015063/50000000000000 : ℝ)*(major0) + (2123753075015063/50000000000000 : ℝ)*(major1) + (2123753075015063/50000000000000 : ℝ)*(major2) + (19059430373/50000000000000 : ℝ)*(sp1) + (40597878529/100000000000000 : ℝ)*(sp2) + (573442443469671/10000000000000 : ℝ)*(sp4) + (5734384361412489/100000000000000 : ℝ)*(sp5) + (5734381709879037/100000000000000 : ℝ)*(sp6) + (2760587497423673/100000000000000 : ℝ)*(sp7) + (2760587497423673/100000000000000 : ℝ)*(f.failure) + (573442443469671/10000000000000 : ℝ)*(f.sum) + (14643042148869/2659375000000000000000000000 : ℝ)*base66 + (5146157612732015439/2127500000000000000000000000000000 : ℝ)*base67 + (885701778775484561/2127500000000000000000000000000000 : ℝ)*base70 + (7837377168270484561/2127500000000000000000000000000000 : ℝ)*base72 + (62235860159701/10637500000000000000000000000 : ℝ)*base74 + (1520832266569515439/2127500000000000000000000000000000 : ℝ)*base75 + (13513780412477984561/2127500000000000000000000000000000 : ℝ)*base78 + (28823975510655484561/2127500000000000000000000000000000 : ℝ)*base80 + (17761985031713/5318750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (47171527/10000000000000000000000 : ℝ)*base89 + (47171527/10000000000000000000000 : ℝ)*base91 + (47171527/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1320_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1879/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10777/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11037/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1320_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1320_s5_0 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2063071287/10000000000 : ℝ)*x 0 + (1353578933/2500000000 : ℝ)*x 1 + (5243472031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063071287/10000000000 : ℝ)^535 ≤ (12558318345697/100000000000000 : ℝ)^407 := by
    have hnat : (2063071287 : ℕ)^535*100000000000000^407 ≤ 12558318345697^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063071287 10000000000 12558318345697 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353578933/2500000000 : ℝ)^535 ≤ (2790127388923/6250000000000 : ℝ)^407 := by
    have hnat : (1353578933 : ℕ)^535*6250000000000^407 ≤ 2790127388923^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353578933 2500000000 2790127388923 6250000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243472031/10000000000 : ℝ)^535 ≤ (42799643417909/100000000000000 : ℝ)^407 := by
    have hnat : (5243472031 : ℕ)^535*100000000000000^407 ≤ 42799643417909^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243472031 10000000000 42799643417909 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2063071287/10000000000 : ℝ), (1353578933/2500000000 : ℝ), (5243472031/10000000000 : ℝ)] ![(12558318345697/100000000000000 : ℝ), (2790127388923/6250000000000 : ℝ), (42799643417909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2063071287/10000000000 : ℝ)|^535 ≤ (12558318345697/100000000000000 : ℝ)^407
        have hw : |(-2063071287/10000000000 : ℝ)|=(2063071287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353578933/2500000000 : ℝ)|^535 ≤ (2790127388923/6250000000000 : ℝ)^407
        have hw : |(1353578933/2500000000 : ℝ)|=(1353578933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243472031/10000000000 : ℝ)|^535 ≤ (42799643417909/100000000000000 : ℝ)^407
        have hw : |(5243472031/10000000000 : ℝ)|=(5243472031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s5_1 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (668685879/1250000000 : ℝ)*x 0 + (-537536127/2500000000 : ℝ)*x 1 + (2621735979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668685879/1250000000 : ℝ)^535 ≤ (8788146817407/20000000000000 : ℝ)^407 := by
    have hnat : (668685879 : ℕ)^535*20000000000000^407 ≤ 8788146817407^407*1250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668685879 1250000000 8788146817407 20000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537536127/2500000000 : ℝ)^535 ≤ (2651924653337/20000000000000 : ℝ)^407 := by
    have hnat : (537536127 : ℕ)^535*20000000000000^407 ≤ 2651924653337^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537536127 2500000000 2651924653337 20000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621735979/5000000000 : ℝ)^535 ≤ (42799642634653/100000000000000 : ℝ)^407 := by
    have hnat : (2621735979 : ℕ)^535*100000000000000^407 ≤ 42799642634653^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621735979 5000000000 42799642634653 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668685879/1250000000 : ℝ), (-537536127/2500000000 : ℝ), (2621735979/5000000000 : ℝ)] ![(8788146817407/20000000000000 : ℝ), (2651924653337/20000000000000 : ℝ), (42799642634653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668685879/1250000000 : ℝ)|^535 ≤ (8788146817407/20000000000000 : ℝ)^407
        have hw : |(668685879/1250000000 : ℝ)|=(668685879/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-537536127/2500000000 : ℝ)|^535 ≤ (2651924653337/20000000000000 : ℝ)^407
        have hw : |(-537536127/2500000000 : ℝ)|=(537536127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621735979/5000000000 : ℝ)|^535 ≤ (42799642634653/100000000000000 : ℝ)^407
        have hw : |(2621735979/5000000000 : ℝ)|=(2621735979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s5_2 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (42795899/80000000 : ℝ)*x 0 + (2621735909/5000000000 : ℝ)*x 1 + (-537536059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42795899/80000000 : ℝ)^535 ≤ (43940737790503/100000000000000 : ℝ)^407 := by
    have hnat : (42795899 : ℕ)^535*100000000000000^407 ≤ 43940737790503^407*80000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42795899 80000000 43940737790503 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621735909/5000000000 : ℝ)^535 ≤ (42799641132519/100000000000000 : ℝ)^407 := by
    have hnat : (2621735909 : ℕ)^535*100000000000000^407 ≤ 42799641132519^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621735909 5000000000 42799641132519 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537536059/2500000000 : ℝ)^535 ≤ (1325962106177/10000000000000 : ℝ)^407 := by
    have hnat : (537536059 : ℕ)^535*10000000000000^407 ≤ 1325962106177^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537536059 2500000000 1325962106177 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42795899/80000000 : ℝ), (2621735909/5000000000 : ℝ), (-537536059/2500000000 : ℝ)] ![(43940737790503/100000000000000 : ℝ), (42799641132519/100000000000000 : ℝ), (1325962106177/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42795899/80000000 : ℝ)|^535 ≤ (43940737790503/100000000000000 : ℝ)^407
        have hw : |(42795899/80000000 : ℝ)|=(42795899/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621735909/5000000000 : ℝ)|^535 ≤ (42799641132519/100000000000000 : ℝ)^407
        have hw : |(2621735909/5000000000 : ℝ)|=(2621735909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-537536059/2500000000 : ℝ)|^535 ≤ (1325962106177/10000000000000 : ℝ)^407
        have hw : |(-537536059/2500000000 : ℝ)|=(537536059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s5_3 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2166185773/5000000000 : ℝ)*x 0 + (4158358603/10000000000 : ℝ)*x 1 + (112831089/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166185773/5000000000 : ℝ)^535 ≤ (3330253279883/10000000000000 : ℝ)^407 := by
    have hnat : (2166185773 : ℕ)^535*10000000000000^407 ≤ 3330253279883^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166185773 5000000000 3330253279883 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4158358603/10000000000 : ℝ)^535 ≤ (31555443827829/100000000000000 : ℝ)^407 := by
    have hnat : (4158358603 : ℕ)^535*100000000000000^407 ≤ 31555443827829^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158358603 10000000000 31555443827829 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112831089/250000000 : ℝ)^535 ≤ (7028404670797/20000000000000 : ℝ)^407 := by
    have hnat : (112831089 : ℕ)^535*20000000000000^407 ≤ 7028404670797^407*250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112831089 250000000 7028404670797 20000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166185773/5000000000 : ℝ), (4158358603/10000000000 : ℝ), (112831089/250000000 : ℝ)] ![(3330253279883/10000000000000 : ℝ), (31555443827829/100000000000000 : ℝ), (7028404670797/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166185773/5000000000 : ℝ)|^535 ≤ (3330253279883/10000000000000 : ℝ)^407
        have hw : |(2166185773/5000000000 : ℝ)|=(2166185773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4158358603/10000000000 : ℝ)|^535 ≤ (31555443827829/100000000000000 : ℝ)^407
        have hw : |(4158358603/10000000000 : ℝ)|=(4158358603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112831089/250000000 : ℝ)|^535 ≤ (7028404670797/20000000000000 : ℝ)^407
        have hw : |(112831089/250000000 : ℝ)|=(112831089/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s5_4 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2063084067/10000000000 : ℝ)*x 0 + (5244085791/10000000000 : ℝ)*x 1 + (338356167/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063084067/10000000000 : ℝ)^535 ≤ (2511684121239/20000000000000 : ℝ)^407 := by
    have hnat : (2063084067 : ℕ)^535*20000000000000^407 ≤ 2511684121239^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063084067 10000000000 2511684121239 20000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244085791/10000000000 : ℝ)^535 ≤ (42806228893469/100000000000000 : ℝ)^407 := by
    have hnat : (5244085791 : ℕ)^535*100000000000000^407 ≤ 42806228893469^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244085791 10000000000 42806228893469 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338356167/625000000 : ℝ)^535 ≤ (44635350482139/100000000000000 : ℝ)^407 := by
    have hnat : (338356167 : ℕ)^535*100000000000000^407 ≤ 44635350482139^407*625000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338356167 625000000 44635350482139 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2063084067/10000000000 : ℝ), (5244085791/10000000000 : ℝ), (338356167/625000000 : ℝ)] ![(2511684121239/20000000000000 : ℝ), (42806228893469/100000000000000 : ℝ), (44635350482139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2063084067/10000000000 : ℝ)|^535 ≤ (2511684121239/20000000000000 : ℝ)^407
        have hw : |(-2063084067/10000000000 : ℝ)|=(2063084067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244085791/10000000000 : ℝ)|^535 ≤ (42806228893469/100000000000000 : ℝ)^407
        have hw : |(5244085791/10000000000 : ℝ)|=(5244085791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338356167/625000000 : ℝ)|^535 ≤ (44635350482139/100000000000000 : ℝ)^407
        have hw : |(338356167/625000000 : ℝ)|=(338356167/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s5_5 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305595463/10000000000 : ℝ)*x 0 + (-494979427/2500000000 : ℝ)*x 1 + (2706849291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305595463/10000000000 : ℝ)^535 ≤ (21733718458907/50000000000000 : ℝ)^407 := by
    have hnat : (5305595463 : ℕ)^535*50000000000000^407 ≤ 21733718458907^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305595463 10000000000 21733718458907 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (494979427/2500000000 : ℝ)^535 ≤ (11897213565237/100000000000000 : ℝ)^407 := by
    have hnat : (494979427 : ℕ)^535*100000000000000^407 ≤ 11897213565237^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494979427 2500000000 11897213565237 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706849291/5000000000 : ℝ)^535 ≤ (4463534950673/10000000000000 : ℝ)^407 := by
    have hnat : (2706849291 : ℕ)^535*10000000000000^407 ≤ 4463534950673^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706849291 5000000000 4463534950673 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305595463/10000000000 : ℝ), (-494979427/2500000000 : ℝ), (2706849291/5000000000 : ℝ)] ![(21733718458907/50000000000000 : ℝ), (11897213565237/100000000000000 : ℝ), (4463534950673/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305595463/10000000000 : ℝ)|^535 ≤ (21733718458907/50000000000000 : ℝ)^407
        have hw : |(5305595463/10000000000 : ℝ)|=(5305595463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-494979427/2500000000 : ℝ)|^535 ≤ (11897213565237/100000000000000 : ℝ)^407
        have hw : |(-494979427/2500000000 : ℝ)|=(494979427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706849291/5000000000 : ℝ)|^535 ≤ (4463534950673/10000000000000 : ℝ)^407
        have hw : |(2706849291/5000000000 : ℝ)|=(2706849291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s5_6 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1326398827/2500000000 : ℝ)*x 0 + (5413698721/10000000000 : ℝ)*x 1 + (-61872429/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326398827/2500000000 : ℝ)^535 ≤ (21733717624283/50000000000000 : ℝ)^407 := by
    have hnat : (1326398827 : ℕ)^535*50000000000000^407 ≤ 21733717624283^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326398827 2500000000 21733717624283 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413698721/10000000000 : ℝ)^535 ≤ (8927070202639/20000000000000 : ℝ)^407 := by
    have hnat : (5413698721 : ℕ)^535*20000000000000^407 ≤ 8927070202639^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413698721 10000000000 8927070202639 20000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (61872429/312500000 : ℝ)^535 ≤ (2974303430803/25000000000000 : ℝ)^407 := by
    have hnat : (61872429 : ℕ)^535*25000000000000^407 ≤ 2974303430803^407*312500000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61872429 312500000 2974303430803 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326398827/2500000000 : ℝ), (5413698721/10000000000 : ℝ), (-61872429/312500000 : ℝ)] ![(21733717624283/50000000000000 : ℝ), (8927070202639/20000000000000 : ℝ), (2974303430803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326398827/2500000000 : ℝ)|^535 ≤ (21733717624283/50000000000000 : ℝ)^407
        have hw : |(1326398827/2500000000 : ℝ)|=(1326398827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413698721/10000000000 : ℝ)|^535 ≤ (8927070202639/20000000000000 : ℝ)^407
        have hw : |(5413698721/10000000000 : ℝ)|=(5413698721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-61872429/312500000 : ℝ)|^535 ≤ (2974303430803/25000000000000 : ℝ)^407
        have hw : |(-61872429/312500000 : ℝ)|=(61872429/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s5_7 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (866479523/2000000000 : ℝ)*x 0 + (563996059/1250000000 : ℝ)*x 1 + (4159640431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866479523/2000000000 : ℝ)^535 ≤ (33302796210933/100000000000000 : ℝ)^407 := by
    have hnat : (866479523 : ℕ)^535*100000000000000^407 ≤ 33302796210933^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866479523 2000000000 33302796210933 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563996059/1250000000 : ℝ)^535 ≤ (2195560820133/6250000000000 : ℝ)^407 := by
    have hnat : (563996059 : ℕ)^535*6250000000000^407 ≤ 2195560820133^407*1250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563996059 1250000000 2195560820133 6250000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4159640431/10000000000 : ℝ)^535 ≤ (15784115323599/50000000000000 : ℝ)^407 := by
    have hnat : (4159640431 : ℕ)^535*50000000000000^407 ≤ 15784115323599^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159640431 10000000000 15784115323599 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866479523/2000000000 : ℝ), (563996059/1250000000 : ℝ), (4159640431/10000000000 : ℝ)] ![(33302796210933/100000000000000 : ℝ), (2195560820133/6250000000000 : ℝ), (15784115323599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866479523/2000000000 : ℝ)|^535 ≤ (33302796210933/100000000000000 : ℝ)^407
        have hw : |(866479523/2000000000 : ℝ)|=(866479523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563996059/1250000000 : ℝ)|^535 ≤ (2195560820133/6250000000000 : ℝ)^407
        have hw : |(563996059/1250000000 : ℝ)|=(563996059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4159640431/10000000000 : ℝ)|^535 ≤ (15784115323599/50000000000000 : ℝ)^407
        have hw : |(4159640431/10000000000 : ℝ)|=(4159640431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1320_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11037/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11087/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14703/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11037/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11037/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11037/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11037/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11037/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11037/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11037/100000 : ℝ) ^ (4279/1024 : ℝ) ≤ (10008089550552997/100000000000000000000 : ℝ) := by
    have hpowers : (11037/100000 : ℝ)^4279 ≤ (10008089550552997/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11037 : ℕ)^4279*100000000000000000000^1024 ≤ 10008089550552997^1024*100000^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11037 100000 10008089550552997 100000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11037/100000 : ℝ)) (X := (10008089550552997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3689/25000 : ℝ) ^ (4279/1024 : ℝ) ≤ (1347163120708747/4000000000000000000 : ℝ) := by
    have hpowers : (3689/25000 : ℝ)^4279 ≤ (1347163120708747/4000000000000000000 : ℝ)^1024 := by
      have hnat : (3689 : ℕ)^4279*4000000000000000000^1024 ≤ 1347163120708747^1024*25000^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3689 25000 1347163120708747 4000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3689/25000 : ℝ)) (X := (1347163120708747/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010008089550552997/50000000000000000000 : ℝ) ≤ (2500119741803953/2500000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (50010008089550552997/50000000000000000000 : ℝ)^1024 ≤ (2500119741803953/2500000000000000 : ℝ)^4279 := by
      have hnat : (50010008089550552997 : ℕ)^1024*2500000000000000^4279 ≤ 2500119741803953^4279*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010008089550552997 50000000000000000000 2500119741803953 2500000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500119741803953/2500000000000000 : ℝ)) (X := (50010008089550552997/50000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505460895946033959/12500000000000000000 : ℝ) ≤ (10001045296286829/10000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (12505460895946033959/12500000000000000000 : ℝ)^1024 ≤ (10001045296286829/10000000000000000 : ℝ)^4279 := by
      have hnat : (12505460895946033959 : ℕ)^1024*10000000000000000^4279 ≤ 10001045296286829^4279*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505460895946033959 12500000000000000000 10001045296286829 10000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001045296286829/10000000000000000 : ℝ)) (X := (12505460895946033959/12500000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001347163120708747/2000000000000000000 : ℝ) ≤ (5000805812678923/5000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (2001347163120708747/2000000000000000000 : ℝ)^1024 ≤ (5000805812678923/5000000000000000 : ℝ)^4279 := by
      have hnat : (2001347163120708747 : ℕ)^1024*5000000000000000^4279 ≤ 5000805812678923^4279*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001347163120708747 2000000000000000000 5000805812678923 5000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000805812678923/5000000000000000 : ℝ)) (X := (2001347163120708747/2000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10008089550552997/100000000000000000000 : ℝ) ≤ ((3717928013116197557/3719000000000000000 : ℝ)+2*(566329071017/371900000000000 : ℝ)*(11037/100000 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (3717928013116197557/3719000000000000000 : ℝ)+2*(566329071017/371900000000000 : ℝ)*(11037/100000 : ℝ)=(2500119741803953/2500000000000000 : ℝ) by norm_num, show 1+2*(10008089550552997/100000000000000000000 : ℝ)=(50010008089550552997/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1347163120708747/4000000000000000000 : ℝ)+(10008089550552997/100000000000000000000 : ℝ) ≤ ((3717928013116197557/3719000000000000000 : ℝ)+(566329071017/371900000000000 : ℝ)*((3689/25000 : ℝ)+(11037/100000 : ℝ)))^(4279/1024 : ℝ) := by
    rw [show (3717928013116197557/3719000000000000000 : ℝ)+(566329071017/371900000000000 : ℝ)*((3689/25000 : ℝ)+(11037/100000 : ℝ))=(10001045296286829/10000000000000000 : ℝ) by norm_num, show 1+(1347163120708747/4000000000000000000 : ℝ)+(10008089550552997/100000000000000000000 : ℝ)=(12505460895946033959/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1347163120708747/4000000000000000000 : ℝ) ≤ ((3717928013116197557/3719000000000000000 : ℝ)+2*(566329071017/371900000000000 : ℝ)*(3689/25000 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (3717928013116197557/3719000000000000000 : ℝ)+2*(566329071017/371900000000000 : ℝ)*(3689/25000 : ℝ)=(5000805812678923/5000000000000000 : ℝ) by norm_num, show 1+2*(1347163120708747/4000000000000000000 : ℝ)=(2001347163120708747/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3717928013116197557/3719000000000000000 : ℝ)*(X 1 0+X 2 0)+(566329071017/371900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (11037/100000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (3717928013116197557/3719000000000000000 : ℝ)) (alpha := (566329071017/371900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3717928013116197557/3719000000000000000 : ℝ)*(X 0 1+X 2 1)+(566329071017/371900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (11037/100000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (3717928013116197557/3719000000000000000 : ℝ)) (alpha := (566329071017/371900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3717928013116197557/3719000000000000000 : ℝ)*(X 0 2+X 1 2)+(566329071017/371900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (11037/100000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (3717928013116197557/3719000000000000000 : ℝ)) (alpha := (566329071017/371900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2063071287/10000000000 : ℝ)*X 0 0+(1353578933/2500000000 : ℝ)*X 0 1+(5243472031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668685879/1250000000 : ℝ)*X 1 0+(-537536127/2500000000 : ℝ)*X 1 1+(2621735979/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42795899/80000000 : ℝ)*X 2 0+(2621735909/5000000000 : ℝ)*X 2 1+(-537536059/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2166185773/5000000000 : ℝ)*X 0 0+(4158358603/10000000000 : ℝ)*X 0 1+(112831089/250000000 : ℝ)*X 0 2+(2166185773/5000000000 : ℝ)*X 1 0+(4158358603/10000000000 : ℝ)*X 1 1+(112831089/250000000 : ℝ)*X 1 2+(2166185773/5000000000 : ℝ)*X 2 0+(4158358603/10000000000 : ℝ)*X 2 1+(112831089/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2063084067/10000000000 : ℝ)*X 0 0+(5244085791/10000000000 : ℝ)*X 0 1+(338356167/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305595463/10000000000 : ℝ)*X 1 0+(-494979427/2500000000 : ℝ)*X 1 1+(2706849291/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326398827/2500000000 : ℝ)*X 2 0+(5413698721/10000000000 : ℝ)*X 2 1+(-61872429/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((866479523/2000000000 : ℝ)*X 0 0+(563996059/1250000000 : ℝ)*X 0 1+(4159640431/10000000000 : ℝ)*X 0 2+(866479523/2000000000 : ℝ)*X 1 0+(563996059/1250000000 : ℝ)*X 1 1+(4159640431/10000000000 : ℝ)*X 1 2+(866479523/2000000000 : ℝ)*X 2 0+(563996059/1250000000 : ℝ)*X 2 1+(4159640431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5842415086767739519539681/1452734375000000000000000000000 : ℝ) := by norm_num
    linear_combination (797330647/100000000000000 : ℝ)*(base19) + (416993379/50000000000000 : ℝ)*(base23) + (23563651/12500000000000 : ℝ)*(lower2) + (9734323/12500000000000 : ℝ)*(upper5) + (135487005229877/3125000000000 : ℝ)*(major0) + (135487005229877/3125000000000 : ℝ)*(major1) + (135487005229877/3125000000000 : ℝ)*(major2) + (2926657296583479/50000000000000 : ℝ)*(sp0) + (585333356496293/10000000000000 : ℝ)*(sp1) + (731666900331117/12500000000000 : ℝ)*(sp2) + (563564494626803/20000000000000 : ℝ)*(sp3) + (335054199/1562500000000 : ℝ)*(sp4) + (1674342117/100000000000000 : ℝ)*(sp5) + (1938177363/20000000000000 : ℝ)*(sp7) + (281783216402083/10000000000000 : ℝ)*(f.failure) + (2926668018317847/50000000000000 : ℝ)*(f.sum) + (76126122127327/18595000000000000000000000000 : ℝ)*base66 + (97647849226070557/5810937500000000000000000000000 : ℝ)*base67 + (22962729314813733/1452734375000000000000000000000 : ℝ)*base69 + (201073732227481739/11621875000000000000000000000000 : ℝ)*base71 + (41085002947067/18595000000000000000000000000 : ℝ)*base74 + (9878109027927179/726367187500000000000000000000 : ℝ)*base75 + (31009695953268091/2905468750000000000000000000000 : ℝ)*base77 + (61321515989658057/5810937500000000000000000000000 : ℝ)*base79 + (72259452017467/18595000000000000000000000000 : ℝ)*base82 + (1022883/1000000000000000000000 : ℝ)*base90 + (1022883/1000000000000000000000 : ℝ)*base92 + (1022883/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (686143232091257922719037501/92975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1341206831/100000000000000 : ℝ)*(base19) + (132755133/10000000000000 : ℝ)*(base23) + (136423397/100000000000000 : ℝ)*(upper3) + (1540759/2000000000000 : ℝ)*(lower4) + (133627579/100000000000000 : ℝ)*(upper5) + (4367019388934269/100000000000000 : ℝ)*(major0) + (4367019388934269/100000000000000 : ℝ)*(major1) + (4367019388934269/100000000000000 : ℝ)*(major2) + (12501936911/50000000000000 : ℝ)*(sp1) + (2662153517/10000000000000 : ℝ)*(sp2) + (736971953897407/12500000000000 : ℝ)*(sp4) + (2947874643049301/50000000000000 : ℝ)*(sp5) + (1179149536418551/20000000000000 : ℝ)*(sp6) + (283826290069367/10000000000000 : ℝ)*(sp7) + (283826290069367/10000000000000 : ℝ)*(f.failure) + (736971953897407/12500000000000 : ℝ)*(f.sum) + (49487100506737/18595000000000000000000000000 : ℝ)*base66 + (1956139354288710833/371900000000000000000000000000000 : ℝ)*base67 + (765614537343310833/371900000000000000000000000000000 : ℝ)*base69 + (174249758444889167/371900000000000000000000000000000 : ℝ)*base72 + (94460968141013/18595000000000000000000000000 : ℝ)*base73 + (7837026084548110833/371900000000000000000000000000000 : ℝ)*base75 + (90857944161110833/371900000000000000000000000000000 : ℝ)*base77 + (3750871511812610833/371900000000000000000000000000000 : ℝ)*base79 + (19494260149377/18595000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6968567/1000000000000000000000 : ℝ)*base90 + (6968567/1000000000000000000000 : ℝ)*base92 + (6968567/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1320_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11037/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11087/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1320_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1320_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1213/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11087/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1320_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1320_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1320_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1213/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11087/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1320_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

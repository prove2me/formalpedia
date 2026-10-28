-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1260_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:53:41.930342+00:00
-- url     : https://prove2.me/submissions/9202cedf-3c85-4485-8662-a76c259ff705

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
theorem support_rectangle_w1260_s0_0 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1855018731/10000000000 : ℝ)*x 0 + (3013728799/5000000000 : ℝ)*x 1 + (4795212243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1855018731/10000000000 : ℝ)^8453 ≤ (2164873482541/20000000000000 : ℝ)^6405 := by
    have hnat : (1855018731 : ℕ)^8453*20000000000000^6405 ≤ 2164873482541^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855018731 10000000000 2164873482541 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3013728799/5000000000 : ℝ)^8453 ≤ (51266305344793/100000000000000 : ℝ)^6405 := by
    have hnat : (3013728799 : ℕ)^8453*100000000000000^6405 ≤ 51266305344793^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3013728799 5000000000 51266305344793 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4795212243/10000000000 : ℝ)^8453 ≤ (18954663617109/50000000000000 : ℝ)^6405 := by
    have hnat : (4795212243 : ℕ)^8453*50000000000000^6405 ≤ 18954663617109^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795212243 10000000000 18954663617109 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1855018731/10000000000 : ℝ), (3013728799/5000000000 : ℝ), (4795212243/10000000000 : ℝ)] ![(2164873482541/20000000000000 : ℝ), (51266305344793/100000000000000 : ℝ), (18954663617109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1855018731/10000000000 : ℝ)|^8453 ≤ (2164873482541/20000000000000 : ℝ)^6405
        have hw : |(-1855018731/10000000000 : ℝ)|=(1855018731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3013728799/5000000000 : ℝ)|^8453 ≤ (51266305344793/100000000000000 : ℝ)^6405
        have hw : |(3013728799/5000000000 : ℝ)|=(3013728799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4795212243/10000000000 : ℝ)|^8453 ≤ (18954663617109/50000000000000 : ℝ)^6405
        have hw : |(4795212243/10000000000 : ℝ)|=(4795212243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s0_1 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2755072689/5000000000 : ℝ)*x 0 + (-511796533/2000000000 : ℝ)*x 1 + (4795212213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755072689/5000000000 : ℝ)^8453 ≤ (11385180047493/25000000000000 : ℝ)^6405 := by
    have hnat : (2755072689 : ℕ)^8453*25000000000000^6405 ≤ 11385180047493^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755072689 5000000000 11385180047493 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (511796533/2000000000 : ℝ)^8453 ≤ (1654995287947/10000000000000 : ℝ)^6405 := by
    have hnat : (511796533 : ℕ)^8453*10000000000000^6405 ≤ 1654995287947^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511796533 2000000000 1654995287947 10000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4795212213/10000000000 : ℝ)^8453 ≤ (37909326921213/100000000000000 : ℝ)^6405 := by
    have hnat : (4795212213 : ℕ)^8453*100000000000000^6405 ≤ 37909326921213^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795212213 10000000000 37909326921213 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755072689/5000000000 : ℝ), (-511796533/2000000000 : ℝ), (4795212213/10000000000 : ℝ)] ![(11385180047493/25000000000000 : ℝ), (1654995287947/10000000000000 : ℝ), (37909326921213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755072689/5000000000 : ℝ)|^8453 ≤ (11385180047493/25000000000000 : ℝ)^6405
        have hw : |(2755072689/5000000000 : ℝ)|=(2755072689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-511796533/2000000000 : ℝ)|^8453 ≤ (1654995287947/10000000000000 : ℝ)^6405
        have hw : |(-511796533/2000000000 : ℝ)|=(511796533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4795212213/10000000000 : ℝ)|^8453 ≤ (37909326921213/100000000000000 : ℝ)^6405
        have hw : |(4795212213/10000000000 : ℝ)|=(4795212213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s0_2 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5510145413/10000000000 : ℝ)*x 0 + (2397606107/5000000000 : ℝ)*x 1 + (-2558982619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510145413/10000000000 : ℝ)^8453 ≤ (45540720571737/100000000000000 : ℝ)^6405 := by
    have hnat : (5510145413 : ℕ)^8453*100000000000000^6405 ≤ 45540720571737^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510145413 10000000000 45540720571737 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2397606107/5000000000 : ℝ)^8453 ≤ (18954663465823/50000000000000 : ℝ)^6405 := by
    have hnat : (2397606107 : ℕ)^8453*50000000000000^6405 ≤ 18954663465823^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397606107 5000000000 18954663465823 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2558982619/10000000000 : ℝ)^8453 ≤ (4137488121711/25000000000000 : ℝ)^6405 := by
    have hnat : (2558982619 : ℕ)^8453*25000000000000^6405 ≤ 4137488121711^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2558982619 10000000000 4137488121711 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510145413/10000000000 : ℝ), (2397606107/5000000000 : ℝ), (-2558982619/10000000000 : ℝ)] ![(45540720571737/100000000000000 : ℝ), (18954663465823/50000000000000 : ℝ), (4137488121711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510145413/10000000000 : ℝ)|^8453 ≤ (45540720571737/100000000000000 : ℝ)^6405
        have hw : |(5510145413/10000000000 : ℝ)|=(5510145413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2397606107/5000000000 : ℝ)|^8453 ≤ (18954663465823/50000000000000 : ℝ)^6405
        have hw : |(2397606107/5000000000 : ℝ)|=(2397606107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2558982619/10000000000 : ℝ)|^8453 ≤ (4137488121711/25000000000000 : ℝ)^6405
        have hw : |(-2558982619/10000000000 : ℝ)|=(2558982619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s0_3 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (419161147/1000000000 : ℝ)*x 0 + (3116229339/10000000000 : ℝ)*x 1 + (5624616601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419161147/1000000000 : ℝ)^8453 ≤ (31742218555547/100000000000000 : ℝ)^6405 := by
    have hnat : (419161147 : ℕ)^8453*100000000000000^6405 ≤ 31742218555547^6405*1000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419161147 1000000000 31742218555547 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3116229339/10000000000 : ℝ)^8453 ≤ (4292865812969/20000000000000 : ℝ)^6405 := by
    have hnat : (3116229339 : ℕ)^8453*20000000000000^6405 ≤ 4292865812969^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3116229339 10000000000 4292865812969 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5624616601/10000000000 : ℝ)^8453 ≤ (46793452367533/100000000000000 : ℝ)^6405 := by
    have hnat : (5624616601 : ℕ)^8453*100000000000000^6405 ≤ 46793452367533^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5624616601 10000000000 46793452367533 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419161147/1000000000 : ℝ), (3116229339/10000000000 : ℝ), (5624616601/10000000000 : ℝ)] ![(31742218555547/100000000000000 : ℝ), (4292865812969/20000000000000 : ℝ), (46793452367533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419161147/1000000000 : ℝ)|^8453 ≤ (31742218555547/100000000000000 : ℝ)^6405
        have hw : |(419161147/1000000000 : ℝ)|=(419161147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3116229339/10000000000 : ℝ)|^8453 ≤ (4292865812969/20000000000000 : ℝ)^6405
        have hw : |(3116229339/10000000000 : ℝ)|=(3116229339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5624616601/10000000000 : ℝ)|^8453 ≤ (46793452367533/100000000000000 : ℝ)^6405
        have hw : |(5624616601/10000000000 : ℝ)|=(5624616601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s0_4 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1859825229/10000000000 : ℝ)*x 0 + (19307733/40000000 : ℝ)*x 1 + (1498653721/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1859825229/10000000000 : ℝ)^8453 ≤ (10861397479029/100000000000000 : ℝ)^6405 := by
    have hnat : (1859825229 : ℕ)^8453*100000000000000^6405 ≤ 10861397479029^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859825229 10000000000 10861397479029 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19307733/40000000 : ℝ)^8453 ≤ (19120318913937/50000000000000 : ℝ)^6405 := by
    have hnat : (19307733 : ℕ)^8453*50000000000000^6405 ≤ 19120318913937^6405*40000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19307733 40000000 19120318913937 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1498653721/2500000000 : ℝ)^8453 ≤ (12724491170301/25000000000000 : ℝ)^6405 := by
    have hnat : (1498653721 : ℕ)^8453*25000000000000^6405 ≤ 12724491170301^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498653721 2500000000 12724491170301 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1859825229/10000000000 : ℝ), (19307733/40000000 : ℝ), (1498653721/2500000000 : ℝ)] ![(10861397479029/100000000000000 : ℝ), (19120318913937/50000000000000 : ℝ), (12724491170301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1859825229/10000000000 : ℝ)|^8453 ≤ (10861397479029/100000000000000 : ℝ)^6405
        have hw : |(-1859825229/10000000000 : ℝ)|=(1859825229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(19307733/40000000 : ℝ)|^8453 ≤ (19120318913937/50000000000000 : ℝ)^6405
        have hw : |(19307733/40000000 : ℝ)|=(19307733/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1498653721/2500000000 : ℝ)|^8453 ≤ (12724491170301/25000000000000 : ℝ)^6405
        have hw : |(1498653721/2500000000 : ℝ)|=(1498653721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s0_5 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (258739707/500000000 : ℝ)*x 0 + (-135957759/1000000000 : ℝ)*x 1 + (1498654323/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258739707/500000000 : ℝ)^8453 ≤ (20959471991893/50000000000000 : ℝ)^6405 := by
    have hnat : (258739707 : ℕ)^8453*50000000000000^6405 ≤ 20959471991893^6405*500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258739707 500000000 20959471991893 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135957759/1000000000 : ℝ)^8453 ≤ (897883042559/12500000000000 : ℝ)^6405 := by
    have hnat : (135957759 : ℕ)^8453*12500000000000^6405 ≤ 897883042559^6405*1000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135957759 1000000000 897883042559 12500000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1498654323/2500000000 : ℝ)^8453 ≤ (50897991664027/100000000000000 : ℝ)^6405 := by
    have hnat : (1498654323 : ℕ)^8453*100000000000000^6405 ≤ 50897991664027^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498654323 2500000000 50897991664027 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258739707/500000000 : ℝ), (-135957759/1000000000 : ℝ), (1498654323/2500000000 : ℝ)] ![(20959471991893/50000000000000 : ℝ), (897883042559/12500000000000 : ℝ), (50897991664027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258739707/500000000 : ℝ)|^8453 ≤ (20959471991893/50000000000000 : ℝ)^6405
        have hw : |(258739707/500000000 : ℝ)|=(258739707/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-135957759/1000000000 : ℝ)|^8453 ≤ (897883042559/12500000000000 : ℝ)^6405
        have hw : |(-135957759/1000000000 : ℝ)|=(135957759/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1498654323/2500000000 : ℝ)|^8453 ≤ (50897991664027/100000000000000 : ℝ)^6405
        have hw : |(1498654323/2500000000 : ℝ)|=(1498654323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s0_6 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5174795187/10000000000 : ℝ)*x 0 + (2997307651/5000000000 : ℝ)*x 1 + (-679789591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174795187/10000000000 : ℝ)^8453 ≤ (41918955177023/100000000000000 : ℝ)^6405 := by
    have hnat : (5174795187 : ℕ)^8453*100000000000000^6405 ≤ 41918955177023^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174795187 10000000000 41918955177023 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2997307651/5000000000 : ℝ)^8453 ≤ (50897969365099/100000000000000 : ℝ)^6405 := by
    have hnat : (2997307651 : ℕ)^8453*100000000000000^6405 ≤ 50897969365099^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2997307651 5000000000 50897969365099 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679789591/5000000000 : ℝ)^8453 ≤ (1795768860231/25000000000000 : ℝ)^6405 := by
    have hnat : (679789591 : ℕ)^8453*25000000000000^6405 ≤ 1795768860231^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679789591 5000000000 1795768860231 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174795187/10000000000 : ℝ), (2997307651/5000000000 : ℝ), (-679789591/5000000000 : ℝ)] ![(41918955177023/100000000000000 : ℝ), (50897969365099/100000000000000 : ℝ), (1795768860231/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174795187/10000000000 : ℝ)|^8453 ≤ (41918955177023/100000000000000 : ℝ)^6405
        have hw : |(5174795187/10000000000 : ℝ)|=(5174795187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2997307651/5000000000 : ℝ)|^8453 ≤ (50897969365099/100000000000000 : ℝ)^6405
        have hw : |(2997307651/5000000000 : ℝ)|=(2997307651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-679789591/5000000000 : ℝ)|^8453 ≤ (1795768860231/25000000000000 : ℝ)^6405
        have hw : |(-679789591/5000000000 : ℝ)|=(679789591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s0_7 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4201398041/10000000000 : ℝ)*x 0 + (5560050419/10000000000 : ℝ)*x 1 + (3183078689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4201398041/10000000000 : ℝ)^8453 ≤ (1273602559361/4000000000000 : ℝ)^6405 := by
    have hnat : (4201398041 : ℕ)^8453*4000000000000^6405 ≤ 1273602559361^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4201398041 10000000000 1273602559361 4000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5560050419/10000000000 : ℝ)^8453 ≤ (46085850209061/100000000000000 : ℝ)^6405 := by
    have hnat : (5560050419 : ℕ)^8453*100000000000000^6405 ≤ 46085850209061^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5560050419 10000000000 46085850209061 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3183078689/10000000000 : ℝ)^8453 ≤ (4414817157977/20000000000000 : ℝ)^6405 := by
    have hnat : (3183078689 : ℕ)^8453*20000000000000^6405 ≤ 4414817157977^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3183078689 10000000000 4414817157977 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4201398041/10000000000 : ℝ), (5560050419/10000000000 : ℝ), (3183078689/10000000000 : ℝ)] ![(1273602559361/4000000000000 : ℝ), (46085850209061/100000000000000 : ℝ), (4414817157977/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4201398041/10000000000 : ℝ)|^8453 ≤ (1273602559361/4000000000000 : ℝ)^6405
        have hw : |(4201398041/10000000000 : ℝ)|=(4201398041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5560050419/10000000000 : ℝ)|^8453 ≤ (46085850209061/100000000000000 : ℝ)^6405
        have hw : |(5560050419/10000000000 : ℝ)|=(5560050419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3183078689/10000000000 : ℝ)|^8453 ≤ (4414817157977/20000000000000 : ℝ)^6405
        have hw : |(3183078689/10000000000 : ℝ)|=(3183078689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1260_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (889/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27369/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (2113/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2113 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2113*1^512 ≤ 0^512*1^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2113/512 : ℝ) ≤ (113943680098951189/5000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2113 ≤ (113943680098951189/5000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2113*5000000000000000000^512 ≤ 113943680098951189^512*5^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 113943680098951189 5000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (113943680098951189/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2113 := by
      have hnat : (1 : ℕ)^512*1^2113 ≤ 1^2113*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (5113943680098951189/5000000000000000000 : ℝ) ≤ (2010949762349523/2000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (5113943680098951189/5000000000000000000 : ℝ)^512 ≤ (2010949762349523/2000000000000000 : ℝ)^2113 := by
      have hnat : (5113943680098951189 : ℕ)^512*2000000000000000^2113 ≤ 2010949762349523^2113*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5113943680098951189 5000000000000000000 2010949762349523 2000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2010949762349523/2000000000000000 : ℝ)) (X := (5113943680098951189/5000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2613943680098951189/2500000000000000000 : ℝ) ≤ (1010949762349523/1000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (2613943680098951189/2500000000000000000 : ℝ)^512 ≤ (1010949762349523/1000000000000000 : ℝ)^2113 := by
      have hnat : (2613943680098951189 : ℕ)^512*1000000000000000^2113 ≤ 1010949762349523^2113*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2613943680098951189 2500000000000000000 1010949762349523 1000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1010949762349523/1000000000000000 : ℝ)) (X := (2613943680098951189/2500000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(10949762349523/800000000000000 : ℝ)*(0 : ℝ))^(2113/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(10949762349523/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(113943680098951189/5000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(10949762349523/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2113/512 : ℝ) := by
    rw [show (1 : ℝ)+(10949762349523/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2010949762349523/2000000000000000 : ℝ) by norm_num, show 1+(113943680098951189/5000000000000000000 : ℝ)+(0 : ℝ)=(5113943680098951189/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(113943680098951189/5000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(10949762349523/800000000000000 : ℝ)*(2/5 : ℝ))^(2113/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(10949762349523/800000000000000 : ℝ)*(2/5 : ℝ)=(1010949762349523/1000000000000000 : ℝ) by norm_num, show 1+2*(113943680098951189/5000000000000000000 : ℝ)=(2613943680098951189/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(10949762349523/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10949762349523/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(10949762349523/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10949762349523/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(10949762349523/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10949762349523/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1855018731/10000000000 : ℝ)*X 0 0+(3013728799/5000000000 : ℝ)*X 0 1+(4795212243/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2755072689/5000000000 : ℝ)*X 1 0+(-511796533/2000000000 : ℝ)*X 1 1+(4795212213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5510145413/10000000000 : ℝ)*X 2 0+(2397606107/5000000000 : ℝ)*X 2 1+(-2558982619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((419161147/1000000000 : ℝ)*X 0 0+(3116229339/10000000000 : ℝ)*X 0 1+(5624616601/10000000000 : ℝ)*X 0 2+(419161147/1000000000 : ℝ)*X 1 0+(3116229339/10000000000 : ℝ)*X 1 1+(5624616601/10000000000 : ℝ)*X 1 2+(419161147/1000000000 : ℝ)*X 2 0+(3116229339/10000000000 : ℝ)*X 2 1+(5624616601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1859825229/10000000000 : ℝ)*X 0 0+(19307733/40000000 : ℝ)*X 0 1+(1498653721/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((258739707/500000000 : ℝ)*X 1 0+(-135957759/1000000000 : ℝ)*X 1 1+(1498654323/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5174795187/10000000000 : ℝ)*X 2 0+(2997307651/5000000000 : ℝ)*X 2 1+(-679789591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4201398041/10000000000 : ℝ)*X 0 0+(5560050419/10000000000 : ℝ)*X 0 1+(3183078689/10000000000 : ℝ)*X 0 2+(4201398041/10000000000 : ℝ)*X 1 0+(5560050419/10000000000 : ℝ)*X 1 1+(3183078689/10000000000 : ℝ)*X 1 2+(4201398041/10000000000 : ℝ)*X 2 0+(5560050419/10000000000 : ℝ)*X 2 1+(3183078689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38284993158929152431681/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (688079/781250000000 : ℝ)*(base1) + (1859212991/100000000000000 : ℝ)*(base19) + (1730506103/100000000000000 : ℝ)*(base23) + (66930847/50000000000000 : ℝ)*(base24) + (433178501/100000000000000 : ℝ)*(upper3) + (302551240882249/50000000000000 : ℝ)*(major0) + (302551240882249/50000000000000 : ℝ)*(major1) + (302551240882249/50000000000000 : ℝ)*(major2) + (81153301617031/10000000000000 : ℝ)*(sp0) + (811535152869451/100000000000000 : ℝ)*(sp1) + (405767573857323/50000000000000 : ℝ)*(sp2) + (398664375271713/100000000000000 : ℝ)*(sp3) + (1020996561/25000000000000 : ℝ)*(sp4) + (1616433717/50000000000000 : ℝ)*(sp7) + (199333848106629/50000000000000 : ℝ)*(f.failure) + (811537012082443/100000000000000 : ℝ)*(f.sum) + (49686744042773/20000000000000000000000000000 : ℝ)*base66 + (114389213002773/40000000000000000000000000000 : ℝ)*base68 + (67070321717227/40000000000000000000000000000 : ℝ)*base69 + (64566070962773/40000000000000000000000000000 : ℝ)*base72 + (66327888442773/20000000000000000000000000000 : ℝ)*base74 + (2628560237227/40000000000000000000000000000 : ℝ)*base75 + (273556923762773/40000000000000000000000000000 : ℝ)*base78 + (478715527562773/40000000000000000000000000000 : ℝ)*base80 + (39404048982773/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (9943957/5000000000000000000000 : ℝ)*base90 + (9943957/5000000000000000000000 : ℝ)*base92 + (9943957/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7324681035044613962103/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (231252543/100000000000000 : ℝ)*(base1) + (1293836593/100000000000000 : ℝ)*(base19) + (1454647337/100000000000000 : ℝ)*(base23) + (290603127/100000000000000 : ℝ)*(upper3) + (39909392203829/6250000000000 : ℝ)*(major0) + (39909392203829/6250000000000 : ℝ)*(major1) + (39909392203829/6250000000000 : ℝ)*(major2) + (492279157/20000000000000 : ℝ)*(sp1) + (1134559749/50000000000000 : ℝ)*(sp2) + (14323163/25000000000000 : ℝ)*(sp3) + (856396036681381/100000000000000 : ℝ)*(sp4) + (42819602509823/5000000000000 : ℝ)*(sp5) + (428196040831001/50000000000000 : ℝ)*(sp6) + (420704261223661/100000000000000 : ℝ)*(sp7) + (84140909953771/20000000000000 : ℝ)*(f.failure) + (428197902714419/50000000000000 : ℝ)*(f.sum) + (9069556306433/2500000000000000000000000000 : ℝ)*base66 + (38830539261433/5000000000000000000000000000 : ℝ)*base68 + (28742298501433/5000000000000000000000000000 : ℝ)*base70 + (36776756431433/5000000000000000000000000000 : ℝ)*base72 + (9557249481433/2500000000000000000000000000 : ℝ)*base74 + (48060467106433/5000000000000000000000000000 : ℝ)*base76 + (22580611021433/5000000000000000000000000000 : ℝ)*base78 + (13887963891433/5000000000000000000000000000 : ℝ)*base80 + (12096364713933/2500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1569243/2000000000000000000000 : ℝ)*base90 + (1569243/2000000000000000000000 : ℝ)*base92 + (1569243/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1260_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (889/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27369/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1260_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1260_s1_0 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-51277987/250000000 : ℝ)*x 0 + (5671120189/10000000000 : ℝ)*x 1 + (2513010997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51277987/250000000 : ℝ)^8453 ≤ (12359472461577/100000000000000 : ℝ)^6405 := by
    have hnat : (51277987 : ℕ)^8453*100000000000000^6405 ≤ 12359472461577^6405*250000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51277987 250000000 12359472461577 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5671120189/10000000000 : ℝ)^8453 ≤ (47304713729567/100000000000000 : ℝ)^6405 := by
    have hnat : (5671120189 : ℕ)^8453*100000000000000^6405 ≤ 47304713729567^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5671120189 10000000000 47304713729567 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2513010997/5000000000 : ℝ)^8453 ≤ (4033581379351/10000000000000 : ℝ)^6405 := by
    have hnat : (2513010997 : ℕ)^8453*10000000000000^6405 ≤ 4033581379351^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513010997 5000000000 4033581379351 10000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51277987/250000000 : ℝ), (5671120189/10000000000 : ℝ), (2513010997/5000000000 : ℝ)] ![(12359472461577/100000000000000 : ℝ), (47304713729567/100000000000000 : ℝ), (4033581379351/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51277987/250000000 : ℝ)|^8453 ≤ (12359472461577/100000000000000 : ℝ)^6405
        have hw : |(-51277987/250000000 : ℝ)|=(51277987/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5671120189/10000000000 : ℝ)|^8453 ≤ (47304713729567/100000000000000 : ℝ)^6405
        have hw : |(5671120189/10000000000 : ℝ)|=(5671120189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2513010997/5000000000 : ℝ)|^8453 ≤ (4033581379351/10000000000000 : ℝ)^6405
        have hw : |(2513010997/5000000000 : ℝ)|=(2513010997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s1_1 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2706341359/5000000000 : ℝ)*x 0 + (-599308423/2500000000 : ℝ)*x 1 + (5026022331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706341359/5000000000 : ℝ)^8453 ≤ (8896131281443/20000000000000 : ℝ)^6405 := by
    have hnat : (2706341359 : ℕ)^8453*20000000000000^6405 ≤ 8896131281443^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706341359 5000000000 8896131281443 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (599308423/2500000000 : ℝ)^8453 ≤ (15183526212353/100000000000000 : ℝ)^6405 := by
    have hnat : (599308423 : ℕ)^8453*100000000000000^6405 ≤ 15183526212353^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599308423 2500000000 15183526212353 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5026022331/10000000000 : ℝ)^8453 ≤ (10083954340713/25000000000000 : ℝ)^6405 := by
    have hnat : (5026022331 : ℕ)^8453*25000000000000^6405 ≤ 10083954340713^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5026022331 10000000000 10083954340713 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706341359/5000000000 : ℝ), (-599308423/2500000000 : ℝ), (5026022331/10000000000 : ℝ)] ![(8896131281443/20000000000000 : ℝ), (15183526212353/100000000000000 : ℝ), (10083954340713/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706341359/5000000000 : ℝ)|^8453 ≤ (8896131281443/20000000000000 : ℝ)^6405
        have hw : |(2706341359/5000000000 : ℝ)|=(2706341359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-599308423/2500000000 : ℝ)|^8453 ≤ (15183526212353/100000000000000 : ℝ)^6405
        have hw : |(-599308423/2500000000 : ℝ)|=(599308423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5026022331/10000000000 : ℝ)|^8453 ≤ (10083954340713/25000000000000 : ℝ)^6405
        have hw : |(5026022331/10000000000 : ℝ)|=(5026022331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s1_2 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (676585379/1250000000 : ℝ)*x 0 + (1256505529/2500000000 : ℝ)*x 1 + (-1198616779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676585379/1250000000 : ℝ)^8453 ≤ (11120164953177/25000000000000 : ℝ)^6405 := by
    have hnat : (676585379 : ℕ)^8453*25000000000000^6405 ≤ 11120164953177^6405*1250000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676585379 1250000000 11120164953177 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1256505529/2500000000 : ℝ)^8453 ≤ (1613432603427/4000000000000 : ℝ)^6405 := by
    have hnat : (1256505529 : ℕ)^8453*4000000000000^6405 ≤ 1613432603427^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256505529 2500000000 1613432603427 4000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1198616779/5000000000 : ℝ)^8453 ≤ (1897940636531/12500000000000 : ℝ)^6405 := by
    have hnat : (1198616779 : ℕ)^8453*12500000000000^6405 ≤ 1897940636531^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198616779 5000000000 1897940636531 12500000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676585379/1250000000 : ℝ), (1256505529/2500000000 : ℝ), (-1198616779/5000000000 : ℝ)] ![(11120164953177/25000000000000 : ℝ), (1613432603427/4000000000000 : ℝ), (1897940636531/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676585379/1250000000 : ℝ)|^8453 ≤ (11120164953177/25000000000000 : ℝ)^6405
        have hw : |(676585379/1250000000 : ℝ)|=(676585379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1256505529/2500000000 : ℝ)|^8453 ≤ (1613432603427/4000000000000 : ℝ)^6405
        have hw : |(1256505529/2500000000 : ℝ)|=(1256505529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1198616779/5000000000 : ℝ)|^8453 ≤ (1897940636531/12500000000000 : ℝ)^6405
        have hw : |(-1198616779/5000000000 : ℝ)|=(1198616779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s1_3 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2153643913/5000000000 : ℝ)*x 0 + (739733757/2000000000 : ℝ)*x 1 + (626480799/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153643913/5000000000 : ℝ)^8453 ≤ (16451690153339/50000000000000 : ℝ)^6405 := by
    have hnat : (2153643913 : ℕ)^8453*50000000000000^6405 ≤ 16451690153339^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153643913 5000000000 16451690153339 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (739733757/2000000000 : ℝ)^8453 ≤ (26910879270539/100000000000000 : ℝ)^6405 := by
    have hnat : (739733757 : ℕ)^8453*100000000000000^6405 ≤ 26910879270539^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739733757 2000000000 26910879270539 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (626480799/1250000000 : ℝ)^8453 ≤ (20092870203309/50000000000000 : ℝ)^6405 := by
    have hnat : (626480799 : ℕ)^8453*50000000000000^6405 ≤ 20092870203309^6405*1250000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626480799 1250000000 20092870203309 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153643913/5000000000 : ℝ), (739733757/2000000000 : ℝ), (626480799/1250000000 : ℝ)] ![(16451690153339/50000000000000 : ℝ), (26910879270539/100000000000000 : ℝ), (20092870203309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153643913/5000000000 : ℝ)|^8453 ≤ (16451690153339/50000000000000 : ℝ)^6405
        have hw : |(2153643913/5000000000 : ℝ)|=(2153643913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(739733757/2000000000 : ℝ)|^8453 ≤ (26910879270539/100000000000000 : ℝ)^6405
        have hw : |(739733757/2000000000 : ℝ)|=(739733757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(626480799/1250000000 : ℝ)|^8453 ≤ (20092870203309/50000000000000 : ℝ)^6405
        have hw : |(626480799/1250000000 : ℝ)|=(626480799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s1_4 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-410354933/2000000000 : ℝ)*x 0 + (2517218247/5000000000 : ℝ)*x 1 + (1415636709/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410354933/2000000000 : ℝ)^8453 ≤ (12364683050747/100000000000000 : ℝ)^6405 := by
    have hnat : (410354933 : ℕ)^8453*100000000000000^6405 ≤ 12364683050747^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410354933 2000000000 12364683050747 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2517218247/5000000000 : ℝ)^8453 ≤ (40424959960037/100000000000000 : ℝ)^6405 := by
    have hnat : (2517218247 : ℕ)^8453*100000000000000^6405 ≤ 40424959960037^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2517218247 5000000000 40424959960037 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1415636709/2500000000 : ℝ)^8453 ≤ (47210356975263/100000000000000 : ℝ)^6405 := by
    have hnat : (1415636709 : ℕ)^8453*100000000000000^6405 ≤ 47210356975263^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415636709 2500000000 47210356975263 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410354933/2000000000 : ℝ), (2517218247/5000000000 : ℝ), (1415636709/2500000000 : ℝ)] ![(12364683050747/100000000000000 : ℝ), (40424959960037/100000000000000 : ℝ), (47210356975263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410354933/2000000000 : ℝ)|^8453 ≤ (12364683050747/100000000000000 : ℝ)^6405
        have hw : |(-410354933/2000000000 : ℝ)|=(410354933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2517218247/5000000000 : ℝ)|^8453 ≤ (40424959960037/100000000000000 : ℝ)^6405
        have hw : |(2517218247/5000000000 : ℝ)|=(2517218247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1415636709/2500000000 : ℝ)|^8453 ≤ (47210356975263/100000000000000 : ℝ)^6405
        have hw : |(1415636709/2500000000 : ℝ)|=(1415636709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s1_5 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5246346303/10000000000 : ℝ)*x 0 + (-352141751/2000000000 : ℝ)*x 1 + (2831273623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246346303/10000000000 : ℝ)^8453 ≤ (4268557743271/10000000000000 : ℝ)^6405 := by
    have hnat : (5246346303 : ℕ)^8453*10000000000000^6405 ≤ 4268557743271^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246346303 10000000000 4268557743271 10000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (352141751/2000000000 : ℝ)^8453 ≤ (2020812212903/20000000000000 : ℝ)^6405 := by
    have hnat : (352141751 : ℕ)^8453*20000000000000^6405 ≤ 2020812212903^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352141751 2000000000 2020812212903 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2831273623/5000000000 : ℝ)^8453 ≤ (11802590371639/25000000000000 : ℝ)^6405 := by
    have hnat : (2831273623 : ℕ)^8453*25000000000000^6405 ≤ 11802590371639^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831273623 5000000000 11802590371639 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246346303/10000000000 : ℝ), (-352141751/2000000000 : ℝ), (2831273623/5000000000 : ℝ)] ![(4268557743271/10000000000000 : ℝ), (2020812212903/20000000000000 : ℝ), (11802590371639/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246346303/10000000000 : ℝ)|^8453 ≤ (4268557743271/10000000000000 : ℝ)^6405
        have hw : |(5246346303/10000000000 : ℝ)|=(5246346303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-352141751/2000000000 : ℝ)|^8453 ≤ (2020812212903/20000000000000 : ℝ)^6405
        have hw : |(-352141751/2000000000 : ℝ)|=(352141751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2831273623/5000000000 : ℝ)|^8453 ≤ (11802590371639/25000000000000 : ℝ)^6405
        have hw : |(2831273623/5000000000 : ℝ)|=(2831273623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s1_6 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2623173111/5000000000 : ℝ)*x 0 + (176954593/312500000 : ℝ)*x 1 + (-880354631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2623173111/5000000000 : ℝ)^8453 ≤ (42685576562947/100000000000000 : ℝ)^6405 := by
    have hnat : (2623173111 : ℕ)^8453*100000000000000^6405 ≤ 42685576562947^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623173111 5000000000 42685576562947 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176954593/312500000 : ℝ)^8453 ≤ (5901294814463/12500000000000 : ℝ)^6405 := by
    have hnat : (176954593 : ℕ)^8453*12500000000000^6405 ≤ 5901294814463^6405*312500000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176954593 312500000 5901294814463 12500000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880354631/5000000000 : ℝ)^8453 ≤ (10104064904311/100000000000000 : ℝ)^6405 := by
    have hnat : (880354631 : ℕ)^8453*100000000000000^6405 ≤ 10104064904311^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880354631 5000000000 10104064904311 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2623173111/5000000000 : ℝ), (176954593/312500000 : ℝ), (-880354631/5000000000 : ℝ)] ![(42685576562947/100000000000000 : ℝ), (5901294814463/12500000000000 : ℝ), (10104064904311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2623173111/5000000000 : ℝ)|^8453 ≤ (42685576562947/100000000000000 : ℝ)^6405
        have hw : |(2623173111/5000000000 : ℝ)|=(2623173111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(176954593/312500000 : ℝ)|^8453 ≤ (5901294814463/12500000000000 : ℝ)^6405
        have hw : |(176954593/312500000 : ℝ)|=(176954593/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-880354631/5000000000 : ℝ)|^8453 ≤ (10104064904311/100000000000000 : ℝ)^6405
        have hw : |(-880354631/5000000000 : ℝ)|=(880354631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s1_7 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4308621303/10000000000 : ℝ)*x 0 + (62433973/125000000 : ℝ)*x 1 + (116128791/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308621303/10000000000 : ℝ)^8453 ≤ (32916824519577/100000000000000 : ℝ)^6405 := by
    have hnat : (4308621303 : ℕ)^8453*100000000000000^6405 ≤ 32916824519577^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308621303 10000000000 32916824519577 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62433973/125000000 : ℝ)^8453 ≤ (4000458593269/10000000000000 : ℝ)^6405 := by
    have hnat : (62433973 : ℕ)^8453*10000000000000^6405 ≤ 4000458593269^6405*125000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62433973 125000000 4000458593269 10000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116128791/312500000 : ℝ)^8453 ≤ (13539294769067/50000000000000 : ℝ)^6405 := by
    have hnat : (116128791 : ℕ)^8453*50000000000000^6405 ≤ 13539294769067^6405*312500000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116128791 312500000 13539294769067 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308621303/10000000000 : ℝ), (62433973/125000000 : ℝ), (116128791/312500000 : ℝ)] ![(32916824519577/100000000000000 : ℝ), (4000458593269/10000000000000 : ℝ), (13539294769067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308621303/10000000000 : ℝ)|^8453 ≤ (32916824519577/100000000000000 : ℝ)^6405
        have hw : |(4308621303/10000000000 : ℝ)|=(4308621303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(62433973/125000000 : ℝ)|^8453 ≤ (4000458593269/10000000000000 : ℝ)^6405
        have hw : |(62433973/125000000 : ℝ)|=(62433973/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(116128791/312500000 : ℝ)|^8453 ≤ (13539294769067/50000000000000 : ℝ)^6405
        have hw : |(116128791/312500000 : ℝ)|=(116128791/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1260_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (889/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1257/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19923/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27369/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (889/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27369/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (889/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27369/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (889/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27369/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (889/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27369/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (889/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27369/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (889/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (889/100000 : ℝ) ^ (2113/512 : ℝ) ≤ (342936501273/100000000000000000000 : ℝ) := by
    have hpowers : (889/100000 : ℝ)^2113 ≤ (342936501273/100000000000000000000 : ℝ)^512 := by
      have hnat : (889 : ℕ)^2113*100000000000000000000^512 ≤ 342936501273^512*100000^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        889 100000 342936501273 100000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (889/100000 : ℝ)) (X := (342936501273/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27369/100000 : ℝ) ^ (2113/512 : ℝ) ≤ (118996445669479967/25000000000000000000 : ℝ) := by
    have hpowers : (27369/100000 : ℝ)^2113 ≤ (118996445669479967/25000000000000000000 : ℝ)^512 := by
      have hnat : (27369 : ℕ)^2113*25000000000000000000^512 ≤ 118996445669479967^512*100000^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27369 100000 118996445669479967 25000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27369/100000 : ℝ)) (X := (118996445669479967/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000342936501273/50000000000000000000 : ℝ) ≤ (2500000004154839/2500000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (50000000342936501273/50000000000000000000 : ℝ)^512 ≤ (2500000004154839/2500000000000000 : ℝ)^2113 := by
      have hnat : (50000000342936501273 : ℕ)^512*2500000000000000^2113 ≤ 2500000004154839^2113*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000342936501273 50000000000000000000 2500000004154839 2500000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000004154839/2500000000000000 : ℝ)) (X := (50000000342936501273/50000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100475986125614421141/100000000000000000000 : ℝ) ≤ (5005756428225793/5000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (100475986125614421141/100000000000000000000 : ℝ)^512 ≤ (5005756428225793/5000000000000000 : ℝ)^2113 := by
      have hnat : (100475986125614421141 : ℕ)^512*5000000000000000^2113 ≤ 5005756428225793^2113*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100475986125614421141 100000000000000000000 5005756428225793 5000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005756428225793/5000000000000000 : ℝ)) (X := (100475986125614421141/100000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12618996445669479967/12500000000000000000 : ℝ) ≤ (1252878212035477/1250000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (12618996445669479967/12500000000000000000 : ℝ)^512 ≤ (1252878212035477/1250000000000000 : ℝ)^2113 := by
      have hnat : (12618996445669479967 : ℕ)^512*1250000000000000^2113 ≤ 1252878212035477^2113*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12618996445669479967 12500000000000000000 1252878212035477 1250000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252878212035477/1250000000000000 : ℝ)) (X := (12618996445669479967/12500000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(342936501273/100000000000000000000 : ℝ) ≤ ((13238976530542942097/13240000000000000000 : ℝ)+2*(1151283983223/264800000000000 : ℝ)*(889/100000 : ℝ))^(2113/512 : ℝ) := by
    rw [show (13238976530542942097/13240000000000000000 : ℝ)+2*(1151283983223/264800000000000 : ℝ)*(889/100000 : ℝ)=(2500000004154839/2500000000000000 : ℝ) by norm_num, show 1+2*(342936501273/100000000000000000000 : ℝ)=(50000000342936501273/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(118996445669479967/25000000000000000000 : ℝ)+(342936501273/100000000000000000000 : ℝ) ≤ ((13238976530542942097/13240000000000000000 : ℝ)+(1151283983223/264800000000000 : ℝ)*((27369/100000 : ℝ)+(889/100000 : ℝ)))^(2113/512 : ℝ) := by
    rw [show (13238976530542942097/13240000000000000000 : ℝ)+(1151283983223/264800000000000 : ℝ)*((27369/100000 : ℝ)+(889/100000 : ℝ))=(5005756428225793/5000000000000000 : ℝ) by norm_num, show 1+(118996445669479967/25000000000000000000 : ℝ)+(342936501273/100000000000000000000 : ℝ)=(100475986125614421141/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(118996445669479967/25000000000000000000 : ℝ) ≤ ((13238976530542942097/13240000000000000000 : ℝ)+2*(1151283983223/264800000000000 : ℝ)*(27369/100000 : ℝ))^(2113/512 : ℝ) := by
    rw [show (13238976530542942097/13240000000000000000 : ℝ)+2*(1151283983223/264800000000000 : ℝ)*(27369/100000 : ℝ)=(1252878212035477/1250000000000000 : ℝ) by norm_num, show 1+2*(118996445669479967/25000000000000000000 : ℝ)=(12618996445669479967/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13238976530542942097/13240000000000000000 : ℝ)*(X 1 0+X 2 0)+(1151283983223/264800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (889/100000 : ℝ)) (hi := (27369/100000 : ℝ)) (c := (13238976530542942097/13240000000000000000 : ℝ)) (alpha := (1151283983223/264800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13238976530542942097/13240000000000000000 : ℝ)*(X 0 1+X 2 1)+(1151283983223/264800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (889/100000 : ℝ)) (hi := (27369/100000 : ℝ)) (c := (13238976530542942097/13240000000000000000 : ℝ)) (alpha := (1151283983223/264800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13238976530542942097/13240000000000000000 : ℝ)*(X 0 2+X 1 2)+(1151283983223/264800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (889/100000 : ℝ)) (hi := (27369/100000 : ℝ)) (c := (13238976530542942097/13240000000000000000 : ℝ)) (alpha := (1151283983223/264800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-51277987/250000000 : ℝ)*X 0 0+(5671120189/10000000000 : ℝ)*X 0 1+(2513010997/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2706341359/5000000000 : ℝ)*X 1 0+(-599308423/2500000000 : ℝ)*X 1 1+(5026022331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((676585379/1250000000 : ℝ)*X 2 0+(1256505529/2500000000 : ℝ)*X 2 1+(-1198616779/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2153643913/5000000000 : ℝ)*X 0 0+(739733757/2000000000 : ℝ)*X 0 1+(626480799/1250000000 : ℝ)*X 0 2+(2153643913/5000000000 : ℝ)*X 1 0+(739733757/2000000000 : ℝ)*X 1 1+(626480799/1250000000 : ℝ)*X 1 2+(2153643913/5000000000 : ℝ)*X 2 0+(739733757/2000000000 : ℝ)*X 2 1+(626480799/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-410354933/2000000000 : ℝ)*X 0 0+(2517218247/5000000000 : ℝ)*X 0 1+(1415636709/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5246346303/10000000000 : ℝ)*X 1 0+(-352141751/2000000000 : ℝ)*X 1 1+(2831273623/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2623173111/5000000000 : ℝ)*X 2 0+(176954593/312500000 : ℝ)*X 2 1+(-880354631/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4308621303/10000000000 : ℝ)*X 0 0+(62433973/125000000 : ℝ)*X 0 1+(116128791/312500000 : ℝ)*X 0 2+(4308621303/10000000000 : ℝ)*X 1 0+(62433973/125000000 : ℝ)*X 1 1+(116128791/312500000 : ℝ)*X 1 2+(4308621303/10000000000 : ℝ)*X 2 0+(62433973/125000000 : ℝ)*X 2 1+(116128791/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (84008940412118416163762961/41375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60809/1562500000000 : ℝ)*(base1) + (529946209/100000000000000 : ℝ)*(base19) + (123974767/20000000000000 : ℝ)*(base23) + (9133107/20000000000000 : ℝ)*(upper3) + (59821981/50000000000000 : ℝ)*(upper5) + (72239832875629/6250000000000 : ℝ)*(major0) + (72239832875629/6250000000000 : ℝ)*(major1) + (72239832875629/6250000000000 : ℝ)*(major2) + (775077367021727/50000000000000 : ℝ)*(sp0) + (62006336556467/4000000000000 : ℝ)*(sp1) + (1550158323984049/100000000000000 : ℝ)*(sp2) + (761513720965741/100000000000000 : ℝ)*(sp3) + (4213706207/100000000000000 : ℝ)*(sp4) + (957811899/50000000000000 : ℝ)*(sp7) + (380757820240657/50000000000000 : ℝ)*(f.failure) + (387539735964471/25000000000000 : ℝ)*(f.sum) + (733933432859/1655000000000000000000000000 : ℝ)*base65 + (38243139046945987/82750000000000000000000000000000 : ℝ)*base68 + (294885288801195987/82750000000000000000000000000000 : ℝ)*base70 + (576315587460304013/82750000000000000000000000000000 : ℝ)*base71 + (4629737233241/1655000000000000000000000000 : ℝ)*base74 + (617476814172054013/82750000000000000000000000000000 : ℝ)*base75 + (29336108245804013/82750000000000000000000000000000 : ℝ)*base77 + (590043135648054013/82750000000000000000000000000000 : ℝ)*base79 + (727879449487/206875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (59693281/5000000000000000000000 : ℝ)*base90 + (59693281/5000000000000000000000 : ℝ)*base92 + (59693281/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72626299887216140223537/13240000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1196049/10000000000000 : ℝ)*(base1) + (1023174549/100000000000000 : ℝ)*(base19) + (48268857/5000000000000 : ℝ)*(base23) + (30402193/20000000000000 : ℝ)*(upper3) + (116800547/100000000000000 : ℝ)*(upper5) + (1187092117797813/100000000000000 : ℝ)*(major0) + (1187092117797813/100000000000000 : ℝ)*(major1) + (1187092117797813/100000000000000 : ℝ)*(major2) + (5503140613/100000000000000 : ℝ)*(sp1) + (4455451347/100000000000000 : ℝ)*(sp2) + (199009551885621/12500000000000 : ℝ)*(sp4) + (398017469202329/25000000000000 : ℝ)*(sp5) + (159207098229599/10000000000000 : ℝ)*(sp6) + (391053818832491/50000000000000 : ℝ)*(sp7) + (6110216012699/781250000000 : ℝ)*(f.failure) + (796038201562239/50000000000000 : ℝ)*(f.sum) + (5423294155059/13240000000000000000000000000 : ℝ)*base65 + (8606648109150816139/1324000000000000000000000000000000 : ℝ)*base68 + (6251724194590816139/1324000000000000000000000000000000 : ℝ)*base70 + (10359220760494816139/1324000000000000000000000000000000 : ℝ)*base72 + (29493343445661/13240000000000000000000000000 : ℝ)*base74 + (455115123725183861/1324000000000000000000000000000000 : ℝ)*base75 + (1968398920857183861/1324000000000000000000000000000000 : ℝ)*base77 + (5314689837649183861/1324000000000000000000000000000000 : ℝ)*base79 + (65881501073421/13240000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (366517/78125000000000000000 : ℝ)*base90 + (366517/78125000000000000000 : ℝ)*base92 + (366517/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1260_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (889/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1257/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19923/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1260_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1260_s2_0 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-419653701/2000000000 : ℝ)*x 0 + (1372438399/2500000000 : ℝ)*x 1 + (5177304131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419653701/2000000000 : ℝ)^8453 ≤ (2547158672953/20000000000000 : ℝ)^6405 := by
    have hnat : (419653701 : ℕ)^8453*20000000000000^6405 ≤ 2547158672953^6405*2000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419653701 2000000000 2547158672953 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372438399/2500000000 : ℝ)^8453 ≤ (22659213411401/50000000000000 : ℝ)^6405 := by
    have hnat : (1372438399 : ℕ)^8453*50000000000000^6405 ≤ 22659213411401^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372438399 2500000000 22659213411401 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177304131/10000000000 : ℝ)^8453 ≤ (20972889900581/50000000000000 : ℝ)^6405 := by
    have hnat : (5177304131 : ℕ)^8453*50000000000000^6405 ≤ 20972889900581^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177304131 10000000000 20972889900581 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419653701/2000000000 : ℝ), (1372438399/2500000000 : ℝ), (5177304131/10000000000 : ℝ)] ![(2547158672953/20000000000000 : ℝ), (22659213411401/50000000000000 : ℝ), (20972889900581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419653701/2000000000 : ℝ)|^8453 ≤ (2547158672953/20000000000000 : ℝ)^6405
        have hw : |(-419653701/2000000000 : ℝ)|=(419653701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372438399/2500000000 : ℝ)|^8453 ≤ (22659213411401/50000000000000 : ℝ)^6405
        have hw : |(1372438399/2500000000 : ℝ)|=(1372438399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177304131/10000000000 : ℝ)|^8453 ≤ (20972889900581/50000000000000 : ℝ)^6405
        have hw : |(5177304131/10000000000 : ℝ)|=(5177304131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s2_1 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368959423/10000000000 : ℝ)*x 0 + (-2260014753/10000000000 : ℝ)*x 1 + (5177304301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368959423/10000000000 : ℝ)^8453 ≤ (44007068105213/100000000000000 : ℝ)^6405 := by
    have hnat : (5368959423 : ℕ)^8453*100000000000000^6405 ≤ 44007068105213^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368959423 10000000000 44007068105213 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2260014753/10000000000 : ℝ)^8453 ≤ (14047150259933/100000000000000 : ℝ)^6405 := by
    have hnat : (2260014753 : ℕ)^8453*100000000000000^6405 ≤ 14047150259933^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260014753 10000000000 14047150259933 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177304301/10000000000 : ℝ)^8453 ≤ (20972890809437/50000000000000 : ℝ)^6405 := by
    have hnat : (5177304301 : ℕ)^8453*50000000000000^6405 ≤ 20972890809437^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177304301 10000000000 20972890809437 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368959423/10000000000 : ℝ), (-2260014753/10000000000 : ℝ), (5177304301/10000000000 : ℝ)] ![(44007068105213/100000000000000 : ℝ), (14047150259933/100000000000000 : ℝ), (20972890809437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368959423/10000000000 : ℝ)|^8453 ≤ (44007068105213/100000000000000 : ℝ)^6405
        have hw : |(5368959423/10000000000 : ℝ)|=(5368959423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2260014753/10000000000 : ℝ)|^8453 ≤ (14047150259933/100000000000000 : ℝ)^6405
        have hw : |(-2260014753/10000000000 : ℝ)|=(2260014753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177304301/10000000000 : ℝ)|^8453 ≤ (20972890809437/50000000000000 : ℝ)^6405
        have hw : |(5177304301/10000000000 : ℝ)|=(5177304301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s2_2 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (335559959/625000000 : ℝ)*x 0 + (5177304331/10000000000 : ℝ)*x 1 + (-1130007409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335559959/625000000 : ℝ)^8453 ≤ (11001766812659/25000000000000 : ℝ)^6405 := by
    have hnat : (335559959 : ℕ)^8453*25000000000000^6405 ≤ 11001766812659^6405*625000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335559959 625000000 11001766812659 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177304331/10000000000 : ℝ)^8453 ≤ (41945781939647/100000000000000 : ℝ)^6405 := by
    have hnat : (5177304331 : ℕ)^8453*100000000000000^6405 ≤ 41945781939647^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177304331 10000000000 41945781939647 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130007409/5000000000 : ℝ)^8453 ≤ (14047150793123/100000000000000 : ℝ)^6405 := by
    have hnat : (1130007409 : ℕ)^8453*100000000000000^6405 ≤ 14047150793123^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130007409 5000000000 14047150793123 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335559959/625000000 : ℝ), (5177304331/10000000000 : ℝ), (-1130007409/5000000000 : ℝ)] ![(11001766812659/25000000000000 : ℝ), (41945781939647/100000000000000 : ℝ), (14047150793123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335559959/625000000 : ℝ)|^8453 ≤ (11001766812659/25000000000000 : ℝ)^6405
        have hw : |(335559959/625000000 : ℝ)|=(335559959/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177304331/10000000000 : ℝ)|^8453 ≤ (41945781939647/100000000000000 : ℝ)^6405
        have hw : |(5177304331/10000000000 : ℝ)|=(5177304331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1130007409/5000000000 : ℝ)|^8453 ≤ (14047150793123/100000000000000 : ℝ)^6405
        have hw : |(-1130007409/5000000000 : ℝ)|=(1130007409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s2_3 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1084973659/2500000000 : ℝ)*x 0 + (2016560133/5000000000 : ℝ)*x 1 + (466914917/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084973659/2500000000 : ℝ)^8453 ≤ (6646501091693/20000000000000 : ℝ)^6405 := by
    have hnat : (1084973659 : ℕ)^8453*20000000000000^6405 ≤ 6646501091693^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084973659 2500000000 6646501091693 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016560133/5000000000 : ℝ)^8453 ≤ (30167884778963/100000000000000 : ℝ)^6405 := by
    have hnat : (2016560133 : ℕ)^8453*100000000000000^6405 ≤ 30167884778963^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016560133 5000000000 30167884778963 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (466914917/1000000000 : ℝ)^8453 ≤ (7319921950151/20000000000000 : ℝ)^6405 := by
    have hnat : (466914917 : ℕ)^8453*20000000000000^6405 ≤ 7319921950151^6405*1000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466914917 1000000000 7319921950151 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084973659/2500000000 : ℝ), (2016560133/5000000000 : ℝ), (466914917/1000000000 : ℝ)] ![(6646501091693/20000000000000 : ℝ), (30167884778963/100000000000000 : ℝ), (7319921950151/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084973659/2500000000 : ℝ)|^8453 ≤ (6646501091693/20000000000000 : ℝ)^6405
        have hw : |(1084973659/2500000000 : ℝ)|=(1084973659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2016560133/5000000000 : ℝ)|^8453 ≤ (30167884778963/100000000000000 : ℝ)^6405
        have hw : |(2016560133/5000000000 : ℝ)|=(2016560133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(466914917/1000000000 : ℝ)|^8453 ≤ (7319921950151/20000000000000 : ℝ)^6405
        have hw : |(466914917/1000000000 : ℝ)|=(466914917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s2_4 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2098343259/10000000000 : ℝ)*x 0 + (2589643969/5000000000 : ℝ)*x 1 + (5487751413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098343259/10000000000 : ℝ)^8453 ≤ (12736392181029/100000000000000 : ℝ)^6405 := by
    have hnat : (2098343259 : ℕ)^8453*100000000000000^6405 ≤ 12736392181029^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098343259 10000000000 12736392181029 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589643969/5000000000 : ℝ)^8453 ≤ (4196699281377/10000000000000 : ℝ)^6405 := by
    have hnat : (2589643969 : ℕ)^8453*10000000000000^6405 ≤ 4196699281377^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589643969 5000000000 4196699281377 10000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5487751413/10000000000 : ℝ)^8453 ≤ (5662076873799/12500000000000 : ℝ)^6405 := by
    have hnat : (5487751413 : ℕ)^8453*12500000000000^6405 ≤ 5662076873799^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487751413 10000000000 5662076873799 12500000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2098343259/10000000000 : ℝ), (2589643969/5000000000 : ℝ), (5487751413/10000000000 : ℝ)] ![(12736392181029/100000000000000 : ℝ), (4196699281377/10000000000000 : ℝ), (5662076873799/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2098343259/10000000000 : ℝ)|^8453 ≤ (12736392181029/100000000000000 : ℝ)^6405
        have hw : |(-2098343259/10000000000 : ℝ)|=(2098343259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589643969/5000000000 : ℝ)|^8453 ≤ (4196699281377/10000000000000 : ℝ)^6405
        have hw : |(2589643969/5000000000 : ℝ)|=(2589643969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5487751413/10000000000 : ℝ)|^8453 ≤ (5662076873799/12500000000000 : ℝ)^6405
        have hw : |(5487751413/10000000000 : ℝ)|=(5487751413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s2_5 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (528907939/1000000000 : ℝ)*x 0 + (-15596539/80000000 : ℝ)*x 1 + (2743875729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528907939/1000000000 : ℝ)^8453 ≤ (4314503388271/10000000000000 : ℝ)^6405 := by
    have hnat : (528907939 : ℕ)^8453*10000000000000^6405 ≤ 4314503388271^6405*1000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528907939 1000000000 4314503388271 10000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15596539/80000000 : ℝ)^8453 ≤ (2311670126043/20000000000000 : ℝ)^6405 := by
    have hnat : (15596539 : ℕ)^8453*20000000000000^6405 ≤ 2311670126043^6405*80000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15596539 80000000 2311670126043 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2743875729/5000000000 : ℝ)^8453 ≤ (9059323096119/20000000000000 : ℝ)^6405 := by
    have hnat : (2743875729 : ℕ)^8453*20000000000000^6405 ≤ 9059323096119^6405*5000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743875729 5000000000 9059323096119 20000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528907939/1000000000 : ℝ), (-15596539/80000000 : ℝ), (2743875729/5000000000 : ℝ)] ![(4314503388271/10000000000000 : ℝ), (2311670126043/20000000000000 : ℝ), (9059323096119/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528907939/1000000000 : ℝ)|^8453 ≤ (4314503388271/10000000000000 : ℝ)^6405
        have hw : |(528907939/1000000000 : ℝ)|=(528907939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15596539/80000000 : ℝ)|^8453 ≤ (2311670126043/20000000000000 : ℝ)^6405
        have hw : |(-15596539/80000000 : ℝ)|=(15596539/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2743875729/5000000000 : ℝ)|^8453 ≤ (9059323096119/20000000000000 : ℝ)^6405
        have hw : |(2743875729/5000000000 : ℝ)|=(2743875729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s2_6 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (33056747/62500000 : ℝ)*x 0 + (5487751567/10000000000 : ℝ)*x 1 + (-1949567043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33056747/62500000 : ℝ)^8453 ≤ (10786258820563/25000000000000 : ℝ)^6405 := by
    have hnat : (33056747 : ℕ)^8453*25000000000000^6405 ≤ 10786258820563^6405*62500000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33056747 62500000 10786258820563 25000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5487751567/10000000000 : ℝ)^8453 ≤ (22648308333987/50000000000000 : ℝ)^6405 := by
    have hnat : (5487751567 : ℕ)^8453*50000000000000^6405 ≤ 22648308333987^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487751567 10000000000 22648308333987 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1949567043/10000000000 : ℝ)^8453 ≤ (462333921301/4000000000000 : ℝ)^6405 := by
    have hnat : (1949567043 : ℕ)^8453*4000000000000^6405 ≤ 462333921301^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949567043 10000000000 462333921301 4000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33056747/62500000 : ℝ), (5487751567/10000000000 : ℝ), (-1949567043/10000000000 : ℝ)] ![(10786258820563/25000000000000 : ℝ), (22648308333987/50000000000000 : ℝ), (462333921301/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33056747/62500000 : ℝ)|^8453 ≤ (10786258820563/25000000000000 : ℝ)^6405
        have hw : |(33056747/62500000 : ℝ)|=(33056747/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5487751567/10000000000 : ℝ)|^8453 ≤ (22648308333987/50000000000000 : ℝ)^6405
        have hw : |(5487751567/10000000000 : ℝ)|=(5487751567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1949567043/10000000000 : ℝ)|^8453 ≤ (462333921301/4000000000000 : ℝ)^6405
        have hw : |(-1949567043/10000000000 : ℝ)|=(1949567043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1260_s2_7 (p : ℝ) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4340046357/10000000000 : ℝ)*x 0 + (1166277839/2500000000 : ℝ)*x 1 + (1009298769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340046357/10000000000 : ℝ)^8453 ≤ (16617019373269/50000000000000 : ℝ)^6405 := by
    have hnat : (4340046357 : ℕ)^8453*50000000000000^6405 ≤ 16617019373269^6405*10000000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340046357 10000000000 16617019373269 50000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1166277839/2500000000 : ℝ)^8453 ≤ (456973054331/1250000000000 : ℝ)^6405 := by
    have hnat : (1166277839 : ℕ)^8453*1250000000000^6405 ≤ 456973054331^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166277839 2500000000 456973054331 1250000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1009298769/2500000000 : ℝ)^8453 ≤ (30208116898691/100000000000000 : ℝ)^6405 := by
    have hnat : (1009298769 : ℕ)^8453*100000000000000^6405 ≤ 30208116898691^6405*2500000000^8453 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009298769 2500000000 30208116898691 100000000000000 8453 6405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8453/2048 : ℝ)) 8453 6405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340046357/10000000000 : ℝ), (1166277839/2500000000 : ℝ), (1009298769/2500000000 : ℝ)] ![(16617019373269/50000000000000 : ℝ), (456973054331/1250000000000 : ℝ), (30208116898691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340046357/10000000000 : ℝ)|^8453 ≤ (16617019373269/50000000000000 : ℝ)^6405
        have hw : |(4340046357/10000000000 : ℝ)|=(4340046357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1166277839/2500000000 : ℝ)|^8453 ≤ (456973054331/1250000000000 : ℝ)^6405
        have hw : |(1166277839/2500000000 : ℝ)|=(1166277839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1009298769/2500000000 : ℝ)|^8453 ≤ (30208116898691/100000000000000 : ℝ)^6405
        have hw : |(1009298769/2500000000 : ℝ)|=(1009298769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1260_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19923/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1257/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2393/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16177/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19923/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1257/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19923/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1257/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19923/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1257/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19923/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1257/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19923/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1257/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19923/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1257/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1257/20000 : ℝ) ^ (2113/512 : ℝ) ≤ (274537855541551/25000000000000000000 : ℝ) := by
    have hpowers : (1257/20000 : ℝ)^2113 ≤ (274537855541551/25000000000000000000 : ℝ)^512 := by
      have hnat : (1257 : ℕ)^2113*25000000000000000000^512 ≤ 274537855541551^512*20000^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1257 20000 274537855541551 25000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1257/20000 : ℝ)) (X := (274537855541551/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hpowhi : (19923/100000 : ℝ) ^ (2113/512 : ℝ) ≤ (128371860032678591/100000000000000000000 : ℝ) := by
    have hpowers : (19923/100000 : ℝ)^2113 ≤ (128371860032678591/100000000000000000000 : ℝ)^512 := by
      have hnat : (19923 : ℕ)^2113*100000000000000000000^512 ≤ 128371860032678591^512*100000^2113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19923 100000 128371860032678591 100000000000000000000 2113 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19923/100000 : ℝ)) (X := (128371860032678591/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500274537855541551/12500000000000000000 : ℝ) ≤ (10000053218064357/10000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (12500274537855541551/12500000000000000000 : ℝ)^512 ≤ (10000053218064357/10000000000000000 : ℝ)^2113 := by
      have hnat : (12500274537855541551 : ℕ)^512*10000000000000000^2113 ≤ 10000053218064357^2113*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500274537855541551 12500000000000000000 10000053218064357 10000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000053218064357/10000000000000000 : ℝ)) (X := (12500274537855541551/12500000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20025894002290968959/20000000000000000000 : ℝ) ≤ (1000313564394339/1000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (20025894002290968959/20000000000000000000 : ℝ)^512 ≤ (1000313564394339/1000000000000000 : ℝ)^2113 := by
      have hnat : (20025894002290968959 : ℕ)^512*1000000000000000^2113 ≤ 1000313564394339^2113*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20025894002290968959 20000000000000000000 1000313564394339 1000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000313564394339/1000000000000000 : ℝ)) (X := (20025894002290968959/20000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50128371860032678591/50000000000000000000 : ℝ) ≤ (10006218069822423/10000000000000000 : ℝ) ^ (2113/512 : ℝ) := by
    have hpowers : (50128371860032678591/50000000000000000000 : ℝ)^512 ≤ (10006218069822423/10000000000000000 : ℝ)^2113 := by
      have hnat : (50128371860032678591 : ℕ)^512*10000000000000000^2113 ≤ 10006218069822423^2113*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50128371860032678591 50000000000000000000 10006218069822423 10000000000000000 512 2113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006218069822423/10000000000000000 : ℝ)) (X := (50128371860032678591/50000000000000000000 : ℝ)) (by norm_num) 2113 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(274537855541551/25000000000000000000 : ℝ) ≤ ((11361831641221854663/11365000000000000000 : ℝ)+2*(1027475293011/454600000000000 : ℝ)*(1257/20000 : ℝ))^(2113/512 : ℝ) := by
    rw [show (11361831641221854663/11365000000000000000 : ℝ)+2*(1027475293011/454600000000000 : ℝ)*(1257/20000 : ℝ)=(10000053218064357/10000000000000000 : ℝ) by norm_num, show 1+2*(274537855541551/25000000000000000000 : ℝ)=(12500274537855541551/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(128371860032678591/100000000000000000000 : ℝ)+(274537855541551/25000000000000000000 : ℝ) ≤ ((11361831641221854663/11365000000000000000 : ℝ)+(1027475293011/454600000000000 : ℝ)*((19923/100000 : ℝ)+(1257/20000 : ℝ)))^(2113/512 : ℝ) := by
    rw [show (11361831641221854663/11365000000000000000 : ℝ)+(1027475293011/454600000000000 : ℝ)*((19923/100000 : ℝ)+(1257/20000 : ℝ))=(1000313564394339/1000000000000000 : ℝ) by norm_num, show 1+(128371860032678591/100000000000000000000 : ℝ)+(274537855541551/25000000000000000000 : ℝ)=(20025894002290968959/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(128371860032678591/100000000000000000000 : ℝ) ≤ ((11361831641221854663/11365000000000000000 : ℝ)+2*(1027475293011/454600000000000 : ℝ)*(19923/100000 : ℝ))^(2113/512 : ℝ) := by
    rw [show (11361831641221854663/11365000000000000000 : ℝ)+2*(1027475293011/454600000000000 : ℝ)*(19923/100000 : ℝ)=(10006218069822423/10000000000000000 : ℝ) by norm_num, show 1+2*(128371860032678591/100000000000000000000 : ℝ)=(50128371860032678591/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11361831641221854663/11365000000000000000 : ℝ)*(X 1 0+X 2 0)+(1027475293011/454600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (1257/20000 : ℝ)) (hi := (19923/100000 : ℝ)) (c := (11361831641221854663/11365000000000000000 : ℝ)) (alpha := (1027475293011/454600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11361831641221854663/11365000000000000000 : ℝ)*(X 0 1+X 2 1)+(1027475293011/454600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (1257/20000 : ℝ)) (hi := (19923/100000 : ℝ)) (c := (11361831641221854663/11365000000000000000 : ℝ)) (alpha := (1027475293011/454600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11361831641221854663/11365000000000000000 : ℝ)*(X 0 2+X 1 2)+(1027475293011/454600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2113/512 : ℝ)) (lo := (1257/20000 : ℝ)) (hi := (19923/100000 : ℝ)) (c := (11361831641221854663/11365000000000000000 : ℝ)) (alpha := (1027475293011/454600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-419653701/2000000000 : ℝ)*X 0 0+(1372438399/2500000000 : ℝ)*X 0 1+(5177304131/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5368959423/10000000000 : ℝ)*X 1 0+(-2260014753/10000000000 : ℝ)*X 1 1+(5177304301/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((335559959/625000000 : ℝ)*X 2 0+(5177304331/10000000000 : ℝ)*X 2 1+(-1130007409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1084973659/2500000000 : ℝ)*X 0 0+(2016560133/5000000000 : ℝ)*X 0 1+(466914917/1000000000 : ℝ)*X 0 2+(1084973659/2500000000 : ℝ)*X 1 0+(2016560133/5000000000 : ℝ)*X 1 1+(466914917/1000000000 : ℝ)*X 1 2+(1084973659/2500000000 : ℝ)*X 2 0+(2016560133/5000000000 : ℝ)*X 2 1+(466914917/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2098343259/10000000000 : ℝ)*X 0 0+(2589643969/5000000000 : ℝ)*X 0 1+(5487751413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528907939/1000000000 : ℝ)*X 1 0+(-15596539/80000000 : ℝ)*X 1 1+(2743875729/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33056747/62500000 : ℝ)*X 2 0+(5487751567/10000000000 : ℝ)*X 2 1+(-1949567043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4340046357/10000000000 : ℝ)*X 0 0+(1166277839/2500000000 : ℝ)*X 0 1+(1009298769/2500000000 : ℝ)*X 0 2+(4340046357/10000000000 : ℝ)*X 1 0+(1166277839/2500000000 : ℝ)*X 1 1+(1009298769/2500000000 : ℝ)*X 1 2+(4340046357/10000000000 : ℝ)*X 2 0+(1166277839/2500000000 : ℝ)*X 2 1+(1009298769/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1260_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (302546902571761906899589077/71031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (349277707/50000000000000 : ℝ)*(base19) + (310972453/50000000000000 : ℝ)*(base23) + (7923819/50000000000000 : ℝ)*(lower2) + (24739433/20000000000000 : ℝ)*(upper3) + (43191081/100000000000000 : ℝ)*(upper5) + (596600020282993/25000000000000 : ℝ)*(major0) + (596600020282993/25000000000000 : ℝ)*(major1) + (596600020282993/25000000000000 : ℝ)*(major2) + (3200527773498173/100000000000000 : ℝ)*(sp0) + (320053569489173/10000000000000 : ℝ)*(sp1) + (1600267885751119/50000000000000 : ℝ)*(sp2) + (1572259247485373/100000000000000 : ℝ)*(sp3) + (861994897/10000000000000 : ℝ)*(sp4) + (1094838277/25000000000000 : ℝ)*(sp7) + (786131813419241/50000000000000 : ℝ)*(f.failure) + (400067049180893/12500000000000 : ℝ)*(f.sum) + (3004588504139/11365000000000000000000000000 : ℝ)*base66 + (1403488837114471359/284125000000000000000000000000000 : ℝ)*base67 + (2321437150655653641/284125000000000000000000000000000 : ℝ)*base70 + (1035920601213028641/284125000000000000000000000000000 : ℝ)*base72 + (44224108240803/5682500000000000000000000000 : ℝ)*base73 + (3446311737875778641/284125000000000000000000000000000 : ℝ)*base76 + (1853842627011278641/284125000000000000000000000000000 : ℝ)*base78 + (3696807446026778641/284125000000000000000000000000000 : ℝ)*base80 + (2073007117879/710312500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (59234247/5000000000000000000000 : ℝ)*base89 + (59234247/5000000000000000000000 : ℝ)*base91 + (59234247/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (259701843882781214851239261/28412500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1114970163/50000000000000 : ℝ)*(base19) + (1219991793/50000000000000 : ℝ)*(base23) + (21856579/100000000000000 : ℝ)*(upper2) + (11724521/4000000000000 : ℝ)*(upper3) + (22322967/12500000000000 : ℝ)*(upper5) + (120861087206917/5000000000000 : ℝ)*(major0) + (120861087206917/5000000000000 : ℝ)*(major1) + (120861087206917/5000000000000 : ℝ)*(major2) + (4687946947/20000000000000 : ℝ)*(sp1) + (29335233749/100000000000000 : ℝ)*(sp2) + (1620936455797653/50000000000000 : ℝ)*(sp4) + (648369448384049/20000000000000 : ℝ)*(sp5) + (324184113637797/10000000000000 : ℝ)*(sp6) + (1592570272001097/100000000000000 : ℝ)*(sp7) + (1592570272001097/100000000000000 : ℝ)*(f.failure) + (1620936455797653/50000000000000 : ℝ)*(f.sum) + (3667835958799/2273000000000000000000000000 : ℝ)*base65 + (123980667087478971/56825000000000000000000000000000 : ℝ)*base67 + (481143453865728971/56825000000000000000000000000000 : ℝ)*base69 + (295956669686178971/56825000000000000000000000000000 : ℝ)*base71 + (863035572507/568250000000000000000000000 : ℝ)*base73 + (114770229183453971/56825000000000000000000000000000 : ℝ)*base75 + (678277167584353971/56825000000000000000000000000000 : ℝ)*base77 + (324935069574653971/56825000000000000000000000000000 : ℝ)*base79 + (80347619683/1136500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (72059801/10000000000000000000000 : ℝ)*base90 + (72059801/10000000000000000000000 : ℝ)*base92 + (72059801/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1260_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19923/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1257/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2393/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16177/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1260_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1260_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2393/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16177/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1260_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1260_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1260_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2113/512 : ℝ) ≤ p) (hpb : p ≤ (8453/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151781167/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2393/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16177/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1260_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

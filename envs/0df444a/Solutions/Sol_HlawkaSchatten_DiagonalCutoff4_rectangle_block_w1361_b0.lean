-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1361_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:18:00.156792+00:00
-- url     : https://prove2.me/submissions/9100d23c-4bf2-4893-94fb-d4a9470a1add

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
theorem support_rectangle_w1361_s0_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-359593423/2000000000 : ℝ)*x 0 + (5988751031/10000000000 : ℝ)*x 1 + (1203855491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (359593423/2000000000 : ℝ)^4321 ≤ (5275915763289/50000000000000 : ℝ)^3297 := by
    have hnat : (359593423 : ℕ)^4321*50000000000000^3297 ≤ 5275915763289^3297*2000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359593423 2000000000 5275915763289 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5988751031/10000000000 : ℝ)^4321 ≤ (12767920340461/25000000000000 : ℝ)^3297 := by
    have hnat : (5988751031 : ℕ)^4321*25000000000000^3297 ≤ 12767920340461^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5988751031 10000000000 12767920340461 25000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203855491/2500000000 : ℝ)^4321 ≤ (19188243552389/50000000000000 : ℝ)^3297 := by
    have hnat : (1203855491 : ℕ)^4321*50000000000000^3297 ≤ 19188243552389^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203855491 2500000000 19188243552389 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-359593423/2000000000 : ℝ), (5988751031/10000000000 : ℝ), (1203855491/2500000000 : ℝ)] ![(5275915763289/50000000000000 : ℝ), (12767920340461/25000000000000 : ℝ), (19188243552389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-359593423/2000000000 : ℝ)|^4321 ≤ (5275915763289/50000000000000 : ℝ)^3297
        have hw : |(-359593423/2000000000 : ℝ)|=(359593423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5988751031/10000000000 : ℝ)|^4321 ≤ (12767920340461/25000000000000 : ℝ)^3297
        have hw : |(5988751031/10000000000 : ℝ)|=(5988751031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1203855491/2500000000 : ℝ)|^4321 ≤ (19188243552389/50000000000000 : ℝ)^3297
        have hw : |(1203855491/2500000000 : ℝ)|=(1203855491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s0_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5499686039/10000000000 : ℝ)*x 0 + (-49279327/200000000 : ℝ)*x 1 + (481542247/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5499686039/10000000000 : ℝ)^4321 ≤ (11419067847267/25000000000000 : ℝ)^3297 := by
    have hnat : (5499686039 : ℕ)^4321*25000000000000^3297 ≤ 11419067847267^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499686039 10000000000 11419067847267 25000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49279327/200000000 : ℝ)^4321 ≤ (3189447239313/20000000000000 : ℝ)^3297 := by
    have hnat : (49279327 : ℕ)^4321*20000000000000^3297 ≤ 3189447239313^3297*200000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49279327 200000000 3189447239313 20000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (481542247/1000000000 : ℝ)^4321 ≤ (38376492389799/100000000000000 : ℝ)^3297 := by
    have hnat : (481542247 : ℕ)^4321*100000000000000^3297 ≤ 38376492389799^3297*1000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481542247 1000000000 38376492389799 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5499686039/10000000000 : ℝ), (-49279327/200000000 : ℝ), (481542247/1000000000 : ℝ)] ![(11419067847267/25000000000000 : ℝ), (3189447239313/20000000000000 : ℝ), (38376492389799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5499686039/10000000000 : ℝ)|^4321 ≤ (11419067847267/25000000000000 : ℝ)^3297
        have hw : |(5499686039/10000000000 : ℝ)|=(5499686039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49279327/200000000 : ℝ)|^4321 ≤ (3189447239313/20000000000000 : ℝ)^3297
        have hw : |(-49279327/200000000 : ℝ)|=(49279327/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(481542247/1000000000 : ℝ)|^4321 ≤ (38376492389799/100000000000000 : ℝ)^3297
        have hw : |(481542247/1000000000 : ℝ)|=(481542247/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s0_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5499685907/10000000000 : ℝ)*x 0 + (4815421959/10000000000 : ℝ)*x 1 + (-49279343/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5499685907/10000000000 : ℝ)^4321 ≤ (45676269952283/100000000000000 : ℝ)^3297 := by
    have hnat : (5499685907 : ℕ)^4321*100000000000000^3297 ≤ 45676269952283^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499685907 10000000000 45676269952283 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4815421959/10000000000 : ℝ)^4321 ≤ (7675297410511/20000000000000 : ℝ)^3297 := by
    have hnat : (4815421959 : ℕ)^4321*20000000000000^3297 ≤ 7675297410511^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4815421959 10000000000 7675297410511 20000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49279343/200000000 : ℝ)^4321 ≤ (7973621491221/50000000000000 : ℝ)^3297 := by
    have hnat : (49279343 : ℕ)^4321*50000000000000^3297 ≤ 7973621491221^3297*200000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49279343 200000000 7973621491221 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5499685907/10000000000 : ℝ), (4815421959/10000000000 : ℝ), (-49279343/200000000 : ℝ)] ![(45676269952283/100000000000000 : ℝ), (7675297410511/20000000000000 : ℝ), (7973621491221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5499685907/10000000000 : ℝ)|^4321 ≤ (45676269952283/100000000000000 : ℝ)^3297
        have hw : |(5499685907/10000000000 : ℝ)|=(5499685907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4815421959/10000000000 : ℝ)|^4321 ≤ (7675297410511/20000000000000 : ℝ)^3297
        have hw : |(4815421959/10000000000 : ℝ)|=(4815421959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49279343/200000000 : ℝ)|^4321 ≤ (7973621491221/50000000000000 : ℝ)^3297
        have hw : |(-49279343/200000000 : ℝ)|=(49279343/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s0_3 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1043979087/2500000000 : ℝ)*x 0 + (776419279/2500000000 : ℝ)*x 1 + (1116175819/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1043979087/2500000000 : ℝ)^4321 ≤ (7959812714399/25000000000000 : ℝ)^3297 := by
    have hnat : (1043979087 : ℕ)^4321*25000000000000^3297 ≤ 7959812714399^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043979087 2500000000 7959812714399 25000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776419279/2500000000 : ℝ)^4321 ≤ (10799346555241/50000000000000 : ℝ)^3297 := by
    have hnat : (776419279 : ℕ)^4321*50000000000000^3297 ≤ 10799346555241^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776419279 2500000000 10799346555241 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1116175819/2000000000 : ℝ)^4321 ≤ (46562056013087/100000000000000 : ℝ)^3297 := by
    have hnat : (1116175819 : ℕ)^4321*100000000000000^3297 ≤ 46562056013087^3297*2000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116175819 2000000000 46562056013087 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1043979087/2500000000 : ℝ), (776419279/2500000000 : ℝ), (1116175819/2000000000 : ℝ)] ![(7959812714399/25000000000000 : ℝ), (10799346555241/50000000000000 : ℝ), (46562056013087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1043979087/2500000000 : ℝ)|^4321 ≤ (7959812714399/25000000000000 : ℝ)^3297
        have hw : |(1043979087/2500000000 : ℝ)|=(1043979087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(776419279/2500000000 : ℝ)|^4321 ≤ (10799346555241/50000000000000 : ℝ)^3297
        have hw : |(776419279/2500000000 : ℝ)|=(776419279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1116175819/2000000000 : ℝ)|^4321 ≤ (46562056013087/100000000000000 : ℝ)^3297
        have hw : |(1116175819/2000000000 : ℝ)|=(1116175819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s0_4 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-72093001/400000000 : ℝ)*x 0 + (121139637/250000000 : ℝ)*x 1 + (5957509851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (72093001/400000000 : ℝ)^4321 ≤ (2646340757509/25000000000000 : ℝ)^3297 := by
    have hnat : (72093001 : ℕ)^4321*25000000000000^3297 ≤ 2646340757509^3297*400000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72093001 400000000 2646340757509 25000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121139637/250000000 : ℝ)^4321 ≤ (2418240135009/6250000000000 : ℝ)^3297 := by
    have hnat : (121139637 : ℕ)^4321*6250000000000^3297 ≤ 2418240135009^3297*250000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121139637 250000000 2418240135009 6250000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5957509851/10000000000 : ℝ)^4321 ≤ (12680698697389/25000000000000 : ℝ)^3297 := by
    have hnat : (5957509851 : ℕ)^4321*25000000000000^3297 ≤ 12680698697389^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5957509851 10000000000 12680698697389 25000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-72093001/400000000 : ℝ), (121139637/250000000 : ℝ), (5957509851/10000000000 : ℝ)] ![(2646340757509/25000000000000 : ℝ), (2418240135009/6250000000000 : ℝ), (12680698697389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-72093001/400000000 : ℝ)|^4321 ≤ (2646340757509/25000000000000 : ℝ)^3297
        have hw : |(-72093001/400000000 : ℝ)|=(72093001/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(121139637/250000000 : ℝ)|^4321 ≤ (2418240135009/6250000000000 : ℝ)^3297
        have hw : |(121139637/250000000 : ℝ)|=(121139637/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5957509851/10000000000 : ℝ)|^4321 ≤ (12680698697389/25000000000000 : ℝ)^3297
        have hw : |(5957509851/10000000000 : ℝ)|=(5957509851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s0_5 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2589899511/5000000000 : ℝ)*x 0 + (-1321880823/10000000000 : ℝ)*x 1 + (5957509143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589899511/5000000000 : ℝ)^4321 ≤ (337810125133/800000000000 : ℝ)^3297 := by
    have hnat : (2589899511 : ℕ)^4321*800000000000^3297 ≤ 337810125133^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589899511 5000000000 337810125133 800000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1321880823/10000000000 : ℝ)^4321 ≤ (881368433033/12500000000000 : ℝ)^3297 := by
    have hnat : (1321880823 : ℕ)^4321*12500000000000^3297 ≤ 881368433033^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321880823 10000000000 881368433033 12500000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5957509143/10000000000 : ℝ)^4321 ≤ (1585087090293/3125000000000 : ℝ)^3297 := by
    have hnat : (5957509143 : ℕ)^4321*3125000000000^3297 ≤ 1585087090293^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5957509143 10000000000 1585087090293 3125000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589899511/5000000000 : ℝ), (-1321880823/10000000000 : ℝ), (5957509143/10000000000 : ℝ)] ![(337810125133/800000000000 : ℝ), (881368433033/12500000000000 : ℝ), (1585087090293/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589899511/5000000000 : ℝ)|^4321 ≤ (337810125133/800000000000 : ℝ)^3297
        have hw : |(2589899511/5000000000 : ℝ)|=(2589899511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1321880823/10000000000 : ℝ)|^4321 ≤ (881368433033/12500000000000 : ℝ)^3297
        have hw : |(-1321880823/10000000000 : ℝ)|=(1321880823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5957509143/10000000000 : ℝ)|^4321 ≤ (1585087090293/3125000000000 : ℝ)^3297
        have hw : |(5957509143/10000000000 : ℝ)|=(5957509143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s0_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5179798763/10000000000 : ℝ)*x 0 + (595751011/1000000000 : ℝ)*x 1 + (-660939837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5179798763/10000000000 : ℝ)^4321 ≤ (42226262874461/100000000000000 : ℝ)^3297 := by
    have hnat : (5179798763 : ℕ)^4321*100000000000000^3297 ≤ 42226262874461^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179798763 10000000000 42226262874461 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (595751011/1000000000 : ℝ)^4321 ≤ (25361398839797/50000000000000 : ℝ)^3297 := by
    have hnat : (595751011 : ℕ)^4321*50000000000000^3297 ≤ 25361398839797^3297*1000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595751011 1000000000 25361398839797 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660939837/5000000000 : ℝ)^4321 ≤ (3525469715977/50000000000000 : ℝ)^3297 := by
    have hnat : (660939837 : ℕ)^4321*50000000000000^3297 ≤ 3525469715977^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660939837 5000000000 3525469715977 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5179798763/10000000000 : ℝ), (595751011/1000000000 : ℝ), (-660939837/5000000000 : ℝ)] ![(42226262874461/100000000000000 : ℝ), (25361398839797/50000000000000 : ℝ), (3525469715977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5179798763/10000000000 : ℝ)|^4321 ≤ (42226262874461/100000000000000 : ℝ)^3297
        have hw : |(5179798763/10000000000 : ℝ)|=(5179798763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(595751011/1000000000 : ℝ)|^4321 ≤ (25361398839797/50000000000000 : ℝ)^3297
        have hw : |(595751011/1000000000 : ℝ)|=(595751011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-660939837/5000000000 : ℝ)|^4321 ≤ (3525469715977/50000000000000 : ℝ)^3297
        have hw : |(-660939837/5000000000 : ℝ)|=(660939837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s0_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4185105203/10000000000 : ℝ)*x 0 + (5517249241/10000000000 : ℝ)*x 1 + (792895567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4185105203/10000000000 : ℝ)^4321 ≤ (31931102319199/100000000000000 : ℝ)^3297 := by
    have hnat : (4185105203 : ℕ)^4321*100000000000000^3297 ≤ 31931102319199^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4185105203 10000000000 31931102319199 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5517249241/10000000000 : ℝ)^4321 ≤ (22933768508213/50000000000000 : ℝ)^3297 := by
    have hnat : (5517249241 : ℕ)^4321*50000000000000^3297 ≤ 22933768508213^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517249241 10000000000 22933768508213 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (792895567/2500000000 : ℝ)^4321 ≤ (1387585040811/6250000000000 : ℝ)^3297 := by
    have hnat : (792895567 : ℕ)^4321*6250000000000^3297 ≤ 1387585040811^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792895567 2500000000 1387585040811 6250000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4185105203/10000000000 : ℝ), (5517249241/10000000000 : ℝ), (792895567/2500000000 : ℝ)] ![(31931102319199/100000000000000 : ℝ), (22933768508213/50000000000000 : ℝ), (1387585040811/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4185105203/10000000000 : ℝ)|^4321 ≤ (31931102319199/100000000000000 : ℝ)^3297
        have hw : |(4185105203/10000000000 : ℝ)|=(4185105203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5517249241/10000000000 : ℝ)|^4321 ≤ (22933768508213/50000000000000 : ℝ)^3297
        have hw : |(5517249241/10000000000 : ℝ)|=(5517249241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(792895567/2500000000 : ℝ)|^4321 ≤ (1387585040811/6250000000000 : ℝ)^3297
        have hw : |(792895567/2500000000 : ℝ)|=(792895567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1361_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155477773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (389/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5347/20000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (135/32 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^135 ≤ (0 : ℝ)^32 := by
      have hnat : (0 : ℕ)^135*1^32 ≤ 0^32*1^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (135/32 : ℝ) ≤ (32734869538957301/1562500000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^135 ≤ (32734869538957301/1562500000000000000 : ℝ)^32 := by
      have hnat : (2 : ℕ)^135*1562500000000000000^32 ≤ 32734869538957301^32*5^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 32734869538957301 1562500000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (32734869538957301/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (1 : ℝ)^32 ≤ (1 : ℝ)^135 := by
      have hnat : (1 : ℕ)^32*1^135 ≤ 1^135*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (1595234869538957301/1562500000000000000 : ℝ) ≤ (10049267935583881/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (1595234869538957301/1562500000000000000 : ℝ)^32 ≤ (10049267935583881/10000000000000000 : ℝ)^135 := by
      have hnat : (1595234869538957301 : ℕ)^32*10000000000000000^135 ≤ 10049267935583881^135*1562500000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1595234869538957301 1562500000000000000 10049267935583881 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10049267935583881/10000000000000000 : ℝ)) (X := (1595234869538957301/1562500000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (813984869538957301/781250000000000000 : ℝ) ≤ (5049267935583881/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (813984869538957301/781250000000000000 : ℝ)^32 ≤ (5049267935583881/5000000000000000 : ℝ)^135 := by
      have hnat : (813984869538957301 : ℕ)^32*5000000000000000^135 ≤ 5049267935583881^135*781250000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        813984869538957301 781250000000000000 5049267935583881 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5049267935583881/5000000000000000 : ℝ)) (X := (813984869538957301/781250000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(49267935583881/4000000000000000 : ℝ)*(0 : ℝ))^(135/32 : ℝ) := by
    rw [show (1 : ℝ)+2*(49267935583881/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32734869538957301/1562500000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(49267935583881/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(135/32 : ℝ) := by
    rw [show (1 : ℝ)+(49267935583881/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10049267935583881/10000000000000000 : ℝ) by norm_num, show 1+(32734869538957301/1562500000000000000 : ℝ)+(0 : ℝ)=(1595234869538957301/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32734869538957301/1562500000000000000 : ℝ) ≤ ((1 : ℝ)+2*(49267935583881/4000000000000000 : ℝ)*(2/5 : ℝ))^(135/32 : ℝ) := by
    rw [show (1 : ℝ)+2*(49267935583881/4000000000000000 : ℝ)*(2/5 : ℝ)=(5049267935583881/5000000000000000 : ℝ) by norm_num, show 1+2*(32734869538957301/1562500000000000000 : ℝ)=(813984869538957301/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(49267935583881/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49267935583881/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(49267935583881/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49267935583881/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(49267935583881/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49267935583881/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-359593423/2000000000 : ℝ)*X 0 0+(5988751031/10000000000 : ℝ)*X 0 1+(1203855491/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5499686039/10000000000 : ℝ)*X 1 0+(-49279327/200000000 : ℝ)*X 1 1+(481542247/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5499685907/10000000000 : ℝ)*X 2 0+(4815421959/10000000000 : ℝ)*X 2 1+(-49279343/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1043979087/2500000000 : ℝ)*X 0 0+(776419279/2500000000 : ℝ)*X 0 1+(1116175819/2000000000 : ℝ)*X 0 2+(1043979087/2500000000 : ℝ)*X 1 0+(776419279/2500000000 : ℝ)*X 1 1+(1116175819/2000000000 : ℝ)*X 1 2+(1043979087/2500000000 : ℝ)*X 2 0+(776419279/2500000000 : ℝ)*X 2 1+(1116175819/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-72093001/400000000 : ℝ)*X 0 0+(121139637/250000000 : ℝ)*X 0 1+(5957509851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2589899511/5000000000 : ℝ)*X 1 0+(-1321880823/10000000000 : ℝ)*X 1 1+(5957509143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5179798763/10000000000 : ℝ)*X 2 0+(595751011/1000000000 : ℝ)*X 2 1+(-660939837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4185105203/10000000000 : ℝ)*X 0 0+(5517249241/10000000000 : ℝ)*X 0 1+(792895567/2500000000 : ℝ)*X 0 2+(4185105203/10000000000 : ℝ)*X 1 0+(5517249241/10000000000 : ℝ)*X 1 1+(792895567/2500000000 : ℝ)*X 1 2+(4185105203/10000000000 : ℝ)*X 2 0+(5517249241/10000000000 : ℝ)*X 2 1+(792895567/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (813944735592996741924867/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73386803/50000000000000 : ℝ)*(base1) + (12010577/100000000000000 : ℝ)*(base16) + (464715683/50000000000000 : ℝ)*(base19) + (23024651/2500000000000 : ℝ)*(base23) + (172264361/100000000000000 : ℝ)*(upper3) + (628145849506477/100000000000000 : ℝ)*(major0) + (628145849506477/100000000000000 : ℝ)*(major1) + (628145849506477/100000000000000 : ℝ)*(major2) + (426139613790161/50000000000000 : ℝ)*(sp0) + (426140279180793/50000000000000 : ℝ)*(sp1) + (53267536176093/6250000000000 : ℝ)*(sp2) + (404008411641473/100000000000000 : ℝ)*(sp3) + (604749203/25000000000000 : ℝ)*(sp4) + (376284221/25000000000000 : ℝ)*(sp7) + (404010063551963/100000000000000 : ℝ)*(f.failure) + (852281499803529/100000000000000 : ℝ)*(f.sum) + (231435341097237/200000000000000000000000000000 : ℝ)*base65 + (2138055224697237/400000000000000000000000000000 : ℝ)*base67 + (250283779497237/400000000000000000000000000000 : ℝ)*base69 + (1593988322297237/400000000000000000000000000000 : ℝ)*base71 + (816449523897237/200000000000000000000000000000 : ℝ)*base73 + (1129176220502763/400000000000000000000000000000 : ℝ)*base76 + (697730817497237/400000000000000000000000000000 : ℝ)*base77 + (3513208324697237/400000000000000000000000000000 : ℝ)*base79 + (128401443102763/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (22981601/10000000000000000000000 : ℝ)*base90 + (22981601/10000000000000000000000 : ℝ)*base92 + (22981601/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (123799174807083106838313/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66221443/10000000000000 : ℝ)*(base19) + (104777631/10000000000000 : ℝ)*(base23) + (108883707/25000000000000 : ℝ)*(base39) + (1052941/6250000000000 : ℝ)*(upper3) + (247399683/100000000000000 : ℝ)*(upper5) + (132565741848309/20000000000000 : ℝ)*(major0) + (132565741848309/20000000000000 : ℝ)*(major1) + (331414136853359/50000000000000 : ℝ)*(major2) + (10243273/625000000000 : ℝ)*(sp1) + (862795057/50000000000000 : ℝ)*(sp2) + (224834858656141/25000000000000 : ℝ)*(sp4) + (449668566743227/50000000000000 : ℝ)*(sp5) + (112417137099121/12500000000000 : ℝ)*(sp6) + (53289667748967/12500000000000 : ℝ)*(sp7) + (53289667748967/12500000000000 : ℝ)*(f.failure) + (28104370942481/3125000000000 : ℝ)*(f.sum) + (438832396548703/400000000000000000000000000000 : ℝ)*base65 + (275416878093721/200000000000000000000000000000 : ℝ)*base68 + (668250670547229/80000000000000000000000000000 : ℝ)*base69 + (82327042093721/200000000000000000000000000000 : ℝ)*base72 + (869414626148703/400000000000000000000000000000 : ℝ)*base73 + (192877985907229/80000000000000000000000000000 : ℝ)*base75 + (342765903692771/80000000000000000000000000000 : ℝ)*base78 + (234419327052771/80000000000000000000000000000 : ℝ)*base80 + (227426058867229/40000000000000000000000000000 : ℝ)*base81 + (289509/1250000000000000000000 : ℝ)*base90 + (289509/1250000000000000000000 : ℝ)*base92 + (12789509/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1361_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155477773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (389/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5347/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1361_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1361_s1_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-495011083/2500000000 : ℝ)*x 0 + (2816856231/5000000000 : ℝ)*x 1 + (5053835983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (495011083/2500000000 : ℝ)^4321 ≤ (11973811706643/100000000000000 : ℝ)^3297 := by
    have hnat : (495011083 : ℕ)^4321*100000000000000^3297 ≤ 11973811706643^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495011083 2500000000 11973811706643 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2816856231/5000000000 : ℝ)^4321 ≤ (47140604501351/100000000000000 : ℝ)^3297 := by
    have hnat : (2816856231 : ℕ)^4321*100000000000000^3297 ≤ 47140604501351^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2816856231 5000000000 47140604501351 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5053835983/10000000000 : ℝ)^4321 ≤ (40885583783449/100000000000000 : ℝ)^3297 := by
    have hnat : (5053835983 : ℕ)^4321*100000000000000^3297 ≤ 40885583783449^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5053835983 10000000000 40885583783449 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-495011083/2500000000 : ℝ), (2816856231/5000000000 : ℝ), (5053835983/10000000000 : ℝ)] ![(11973811706643/100000000000000 : ℝ), (47140604501351/100000000000000 : ℝ), (40885583783449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-495011083/2500000000 : ℝ)|^4321 ≤ (11973811706643/100000000000000 : ℝ)^3297
        have hw : |(-495011083/2500000000 : ℝ)|=(495011083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2816856231/5000000000 : ℝ)|^4321 ≤ (47140604501351/100000000000000 : ℝ)^3297
        have hw : |(2816856231/5000000000 : ℝ)|=(2816856231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5053835983/10000000000 : ℝ)|^4321 ≤ (40885583783449/100000000000000 : ℝ)^3297
        have hw : |(5053835983/10000000000 : ℝ)|=(5053835983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s1_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5403742803/10000000000 : ℝ)*x 0 + (-572245749/2500000000 : ℝ)*x 1 + (2526918459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5403742803/10000000000 : ℝ)^4321 ≤ (44634794796733/100000000000000 : ℝ)^3297 := by
    have hnat : (5403742803 : ℕ)^4321*100000000000000^3297 ≤ 44634794796733^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403742803 10000000000 44634794796733 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (572245749/2500000000 : ℝ)^4321 ≤ (7239805744937/50000000000000 : ℝ)^3297 := by
    have hnat : (572245749 : ℕ)^4321*50000000000000^3297 ≤ 7239805744937^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572245749 2500000000 7239805744937 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2526918459/5000000000 : ℝ)^4321 ≤ (20442796848463/50000000000000 : ℝ)^3297 := by
    have hnat : (2526918459 : ℕ)^4321*50000000000000^3297 ≤ 20442796848463^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2526918459 5000000000 20442796848463 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5403742803/10000000000 : ℝ), (-572245749/2500000000 : ℝ), (2526918459/5000000000 : ℝ)] ![(44634794796733/100000000000000 : ℝ), (7239805744937/50000000000000 : ℝ), (20442796848463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5403742803/10000000000 : ℝ)|^4321 ≤ (44634794796733/100000000000000 : ℝ)^3297
        have hw : |(5403742803/10000000000 : ℝ)|=(5403742803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-572245749/2500000000 : ℝ)|^4321 ≤ (7239805744937/50000000000000 : ℝ)^3297
        have hw : |(-572245749/2500000000 : ℝ)|=(572245749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2526918459/5000000000 : ℝ)|^4321 ≤ (20442796848463/50000000000000 : ℝ)^3297
        have hw : |(2526918459/5000000000 : ℝ)|=(2526918459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s1_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2701871497/5000000000 : ℝ)*x 0 + (5053836161/10000000000 : ℝ)*x 1 + (-1144491857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2701871497/5000000000 : ℝ)^4321 ≤ (22317398432193/50000000000000 : ℝ)^3297 := by
    have hnat : (2701871497 : ℕ)^4321*50000000000000^3297 ≤ 22317398432193^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701871497 5000000000 22317398432193 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5053836161/10000000000 : ℝ)^4321 ≤ (127767455221/312500000000 : ℝ)^3297 := by
    have hnat : (5053836161 : ℕ)^4321*312500000000^3297 ≤ 127767455221^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5053836161 10000000000 127767455221 312500000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1144491857/5000000000 : ℝ)^4321 ≤ (14479617442439/100000000000000 : ℝ)^3297 := by
    have hnat : (1144491857 : ℕ)^4321*100000000000000^3297 ≤ 14479617442439^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144491857 5000000000 14479617442439 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2701871497/5000000000 : ℝ), (5053836161/10000000000 : ℝ), (-1144491857/5000000000 : ℝ)] ![(22317398432193/50000000000000 : ℝ), (127767455221/312500000000 : ℝ), (14479617442439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2701871497/5000000000 : ℝ)|^4321 ≤ (22317398432193/50000000000000 : ℝ)^3297
        have hw : |(2701871497/5000000000 : ℝ)|=(2701871497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5053836161/10000000000 : ℝ)|^4321 ≤ (127767455221/312500000000 : ℝ)^3297
        have hw : |(5053836161/10000000000 : ℝ)|=(5053836161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1144491857/5000000000 : ℝ)|^4321 ≤ (14479617442439/100000000000000 : ℝ)^3297
        have hw : |(-1144491857/5000000000 : ℝ)|=(1144491857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s1_3 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (857782771/2000000000 : ℝ)*x 0 + (3717360721/10000000000 : ℝ)*x 1 + (4940638149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857782771/2000000000 : ℝ)^4321 ≤ (2060818736039/6250000000000 : ℝ)^3297 := by
    have hnat : (857782771 : ℕ)^4321*6250000000000^3297 ≤ 2060818736039^3297*2000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857782771 2000000000 2060818736039 6250000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3717360721/10000000000 : ℝ)^4321 ≤ (27337316960419/100000000000000 : ℝ)^3297 := by
    have hnat : (3717360721 : ℕ)^4321*100000000000000^3297 ≤ 27337316960419^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3717360721 10000000000 27337316960419 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4940638149/10000000000 : ℝ)^4321 ≤ (39689583244209/100000000000000 : ℝ)^3297 := by
    have hnat : (4940638149 : ℕ)^4321*100000000000000^3297 ≤ 39689583244209^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4940638149 10000000000 39689583244209 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(857782771/2000000000 : ℝ), (3717360721/10000000000 : ℝ), (4940638149/10000000000 : ℝ)] ![(2060818736039/6250000000000 : ℝ), (27337316960419/100000000000000 : ℝ), (39689583244209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(857782771/2000000000 : ℝ)|^4321 ≤ (2060818736039/6250000000000 : ℝ)^3297
        have hw : |(857782771/2000000000 : ℝ)|=(857782771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3717360721/10000000000 : ℝ)|^4321 ≤ (27337316960419/100000000000000 : ℝ)^3297
        have hw : |(3717360721/10000000000 : ℝ)|=(3717360721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4940638149/10000000000 : ℝ)|^4321 ≤ (39689583244209/100000000000000 : ℝ)^3297
        have hw : |(4940638149/10000000000 : ℝ)|=(4940638149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s1_4 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-990273577/5000000000 : ℝ)*x 0 + (2530503311/5000000000 : ℝ)*x 1 + (2813206649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (990273577/5000000000 : ℝ)^4321 ≤ (11977796944307/100000000000000 : ℝ)^3297 := by
    have hnat : (990273577 : ℕ)^4321*100000000000000^3297 ≤ 11977796944307^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990273577 5000000000 11977796944307 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2530503311/5000000000 : ℝ)^4321 ≤ (20480814148619/50000000000000 : ℝ)^3297 := by
    have hnat : (2530503311 : ℕ)^4321*50000000000000^3297 ≤ 20480814148619^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2530503311 5000000000 20480814148619 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2813206649/5000000000 : ℝ)^4321 ≤ (47060574744829/100000000000000 : ℝ)^3297 := by
    have hnat : (2813206649 : ℕ)^4321*100000000000000^3297 ≤ 47060574744829^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2813206649 5000000000 47060574744829 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-990273577/5000000000 : ℝ), (2530503311/5000000000 : ℝ), (2813206649/5000000000 : ℝ)] ![(11977796944307/100000000000000 : ℝ), (20480814148619/50000000000000 : ℝ), (47060574744829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-990273577/5000000000 : ℝ)|^4321 ≤ (11977796944307/100000000000000 : ℝ)^3297
        have hw : |(-990273577/5000000000 : ℝ)|=(990273577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2530503311/5000000000 : ℝ)|^4321 ≤ (20480814148619/50000000000000 : ℝ)^3297
        have hw : |(2530503311/5000000000 : ℝ)|=(2530503311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2813206649/5000000000 : ℝ)|^4321 ≤ (47060574744829/100000000000000 : ℝ)^3297
        have hw : |(2813206649/5000000000 : ℝ)|=(2813206649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s1_5 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253036669/10000000000 : ℝ)*x 0 + (-1716406429/10000000000 : ℝ)*x 1 + (5626413367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253036669/10000000000 : ℝ)^4321 ≤ (21505225680031/50000000000000 : ℝ)^3297 := by
    have hnat : (5253036669 : ℕ)^4321*50000000000000^3297 ≤ 21505225680031^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253036669 10000000000 21505225680031 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1716406429/10000000000 : ℝ)^4321 ≤ (4964486561517/50000000000000 : ℝ)^3297 := by
    have hnat : (1716406429 : ℕ)^4321*50000000000000^3297 ≤ 4964486561517^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1716406429 10000000000 4964486561517 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5626413367/10000000000 : ℝ)^4321 ≤ (47060575501209/100000000000000 : ℝ)^3297 := by
    have hnat : (5626413367 : ℕ)^4321*100000000000000^3297 ≤ 47060575501209^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5626413367 10000000000 47060575501209 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253036669/10000000000 : ℝ), (-1716406429/10000000000 : ℝ), (5626413367/10000000000 : ℝ)] ![(21505225680031/50000000000000 : ℝ), (4964486561517/50000000000000 : ℝ), (47060575501209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253036669/10000000000 : ℝ)|^4321 ≤ (21505225680031/50000000000000 : ℝ)^3297
        have hw : |(5253036669/10000000000 : ℝ)|=(5253036669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1716406429/10000000000 : ℝ)|^4321 ≤ (4964486561517/50000000000000 : ℝ)^3297
        have hw : |(-1716406429/10000000000 : ℝ)|=(1716406429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5626413367/10000000000 : ℝ)|^4321 ≤ (47060575501209/100000000000000 : ℝ)^3297
        have hw : |(5626413367/10000000000 : ℝ)|=(5626413367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s1_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626518281/5000000000 : ℝ)*x 0 + (2813206727/5000000000 : ℝ)*x 1 + (-343281291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626518281/5000000000 : ℝ)^4321 ≤ (68816720339/160000000000 : ℝ)^3297 := by
    have hnat : (2626518281 : ℕ)^4321*160000000000^3297 ≤ 68816720339^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626518281 5000000000 68816720339 160000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2813206727/5000000000 : ℝ)^4321 ≤ (9412115290981/20000000000000 : ℝ)^3297 := by
    have hnat : (2813206727 : ℕ)^4321*20000000000000^3297 ≤ 9412115290981^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2813206727 5000000000 9412115290981 20000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343281291/2000000000 : ℝ)^4321 ≤ (9928973320151/100000000000000 : ℝ)^3297 := by
    have hnat : (343281291 : ℕ)^4321*100000000000000^3297 ≤ 9928973320151^3297*2000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343281291 2000000000 9928973320151 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626518281/5000000000 : ℝ), (2813206727/5000000000 : ℝ), (-343281291/2000000000 : ℝ)] ![(68816720339/160000000000 : ℝ), (9412115290981/20000000000000 : ℝ), (9928973320151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626518281/5000000000 : ℝ)|^4321 ≤ (68816720339/160000000000 : ℝ)^3297
        have hw : |(2626518281/5000000000 : ℝ)|=(2626518281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2813206727/5000000000 : ℝ)|^4321 ≤ (9412115290981/20000000000000 : ℝ)^3297
        have hw : |(2813206727/5000000000 : ℝ)|=(2813206727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-343281291/2000000000 : ℝ)|^4321 ≤ (9928973320151/100000000000000 : ℝ)^3297
        have hw : |(-343281291/2000000000 : ℝ)|=(343281291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s1_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2144987617/5000000000 : ℝ)*x 0 + (4925512803/10000000000 : ℝ)*x 1 + (3732755909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144987617/5000000000 : ℝ)^4321 ≤ (3298379438663/10000000000000 : ℝ)^3297 := by
    have hnat : (2144987617 : ℕ)^4321*10000000000000^3297 ≤ 3298379438663^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144987617 5000000000 3298379438663 10000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4925512803/10000000000 : ℝ)^4321 ≤ (19765207309779/50000000000000 : ℝ)^3297 := by
    have hnat : (4925512803 : ℕ)^4321*50000000000000^3297 ≤ 19765207309779^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4925512803 10000000000 19765207309779 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3732755909/10000000000 : ℝ)^4321 ≤ (6871447743859/25000000000000 : ℝ)^3297 := by
    have hnat : (3732755909 : ℕ)^4321*25000000000000^3297 ≤ 6871447743859^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3732755909 10000000000 6871447743859 25000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2144987617/5000000000 : ℝ), (4925512803/10000000000 : ℝ), (3732755909/10000000000 : ℝ)] ![(3298379438663/10000000000000 : ℝ), (19765207309779/50000000000000 : ℝ), (6871447743859/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2144987617/5000000000 : ℝ)|^4321 ≤ (3298379438663/10000000000000 : ℝ)^3297
        have hw : |(2144987617/5000000000 : ℝ)|=(2144987617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4925512803/10000000000 : ℝ)|^4321 ≤ (19765207309779/50000000000000 : ℝ)^3297
        have hw : |(4925512803/10000000000 : ℝ)|=(4925512803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3732755909/10000000000 : ℝ)|^4321 ≤ (6871447743859/25000000000000 : ℝ)^3297
        have hw : |(3732755909/10000000000 : ℝ)|=(3732755909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1361_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155477773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5347/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (389/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (883/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19321/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5347/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (389/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5347/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (389/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5347/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (389/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5347/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (389/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5347/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (389/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5347/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (389/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (389/25000 : ℝ) ^ (135/32 : ℝ) ≤ (117899095517/5000000000000000000 : ℝ) := by
    have hpowers : (389/25000 : ℝ)^135 ≤ (117899095517/5000000000000000000 : ℝ)^32 := by
      have hnat : (389 : ℕ)^135*5000000000000000000^32 ≤ 117899095517^32*25000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        389 25000 117899095517 5000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (389/25000 : ℝ)) (X := (117899095517/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hpowhi : (5347/20000 : ℝ) ^ (135/32 : ℝ) ≤ (76563986961568101/20000000000000000000 : ℝ) := by
    have hpowers : (5347/20000 : ℝ)^135 ≤ (76563986961568101/20000000000000000000 : ℝ)^32 := by
      have hnat : (5347 : ℕ)^135*20000000000000000000^32 ≤ 76563986961568101^32*20000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5347 20000 76563986961568101 20000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5347/20000 : ℝ)) (X := (76563986961568101/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500000117899095517/2500000000000000000 : ℝ) ≤ (625000006986613/625000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (2500000117899095517/2500000000000000000 : ℝ)^32 ≤ (625000006986613/625000000000000 : ℝ)^135 := by
      have hnat : (2500000117899095517 : ℕ)^32*625000000000000^135 ≤ 625000006986613^135*2500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500000117899095517 2500000000000000000 625000006986613 625000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000006986613/625000000000000 : ℝ)) (X := (2500000117899095517/2500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (20076564458557950169/20000000000000000000 : ℝ) ≤ (5004530541925907/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (20076564458557950169/20000000000000000000 : ℝ)^32 ≤ (5004530541925907/5000000000000000 : ℝ)^135 := by
      have hnat : (20076564458557950169 : ℕ)^32*5000000000000000^135 ≤ 5004530541925907^135*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20076564458557950169 20000000000000000000 5004530541925907 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004530541925907/5000000000000000 : ℝ)) (X := (20076564458557950169/20000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (10076563986961568101/10000000000000000000 : ℝ) ≤ (500906102795891/500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (10076563986961568101/10000000000000000000 : ℝ)^32 ≤ (500906102795891/500000000000000 : ℝ)^135 := by
      have hnat : (10076563986961568101 : ℕ)^32*500000000000000^135 ≤ 500906102795891^135*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10076563986961568101 10000000000000000000 500906102795891 500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500906102795891/500000000000000 : ℝ)) (X := (10076563986961568101/10000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(117899095517/5000000000000000000 : ℝ) ≤ ((73172957667639/73181152343750 : ℝ)+2*(215737430143/59950000000000 : ℝ)*(389/25000 : ℝ))^(135/32 : ℝ) := by
    rw [show (73172957667639/73181152343750 : ℝ)+2*(215737430143/59950000000000 : ℝ)*(389/25000 : ℝ)=(625000006986613/625000000000000 : ℝ) by norm_num, show 1+2*(117899095517/5000000000000000000 : ℝ)=(2500000117899095517/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(76563986961568101/20000000000000000000 : ℝ)+(117899095517/5000000000000000000 : ℝ) ≤ ((73172957667639/73181152343750 : ℝ)+(215737430143/59950000000000 : ℝ)*((5347/20000 : ℝ)+(389/25000 : ℝ)))^(135/32 : ℝ) := by
    rw [show (73172957667639/73181152343750 : ℝ)+(215737430143/59950000000000 : ℝ)*((5347/20000 : ℝ)+(389/25000 : ℝ))=(5004530541925907/5000000000000000 : ℝ) by norm_num, show 1+(76563986961568101/20000000000000000000 : ℝ)+(117899095517/5000000000000000000 : ℝ)=(20076564458557950169/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(76563986961568101/20000000000000000000 : ℝ) ≤ ((73172957667639/73181152343750 : ℝ)+2*(215737430143/59950000000000 : ℝ)*(5347/20000 : ℝ))^(135/32 : ℝ) := by
    rw [show (73172957667639/73181152343750 : ℝ)+2*(215737430143/59950000000000 : ℝ)*(5347/20000 : ℝ)=(500906102795891/500000000000000 : ℝ) by norm_num, show 1+2*(76563986961568101/20000000000000000000 : ℝ)=(10076563986961568101/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (73172957667639/73181152343750 : ℝ)*(X 1 0+X 2 0)+(215737430143/59950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (389/25000 : ℝ)) (hi := (5347/20000 : ℝ)) (c := (73172957667639/73181152343750 : ℝ)) (alpha := (215737430143/59950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (73172957667639/73181152343750 : ℝ)*(X 0 1+X 2 1)+(215737430143/59950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (389/25000 : ℝ)) (hi := (5347/20000 : ℝ)) (c := (73172957667639/73181152343750 : ℝ)) (alpha := (215737430143/59950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (73172957667639/73181152343750 : ℝ)*(X 0 2+X 1 2)+(215737430143/59950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (389/25000 : ℝ)) (hi := (5347/20000 : ℝ)) (c := (73172957667639/73181152343750 : ℝ)) (alpha := (215737430143/59950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-495011083/2500000000 : ℝ)*X 0 0+(2816856231/5000000000 : ℝ)*X 0 1+(5053835983/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5403742803/10000000000 : ℝ)*X 1 0+(-572245749/2500000000 : ℝ)*X 1 1+(2526918459/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2701871497/5000000000 : ℝ)*X 2 0+(5053836161/10000000000 : ℝ)*X 2 1+(-1144491857/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((857782771/2000000000 : ℝ)*X 0 0+(3717360721/10000000000 : ℝ)*X 0 1+(4940638149/10000000000 : ℝ)*X 0 2+(857782771/2000000000 : ℝ)*X 1 0+(3717360721/10000000000 : ℝ)*X 1 1+(4940638149/10000000000 : ℝ)*X 1 2+(857782771/2000000000 : ℝ)*X 2 0+(3717360721/10000000000 : ℝ)*X 2 1+(4940638149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-990273577/5000000000 : ℝ)*X 0 0+(2530503311/5000000000 : ℝ)*X 0 1+(2813206649/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5253036669/10000000000 : ℝ)*X 1 0+(-1716406429/10000000000 : ℝ)*X 1 1+(5626413367/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2626518281/5000000000 : ℝ)*X 2 0+(2813206727/5000000000 : ℝ)*X 2 1+(-343281291/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2144987617/5000000000 : ℝ)*X 0 0+(4925512803/10000000000 : ℝ)*X 0 1+(3732755909/10000000000 : ℝ)*X 0 2+(2144987617/5000000000 : ℝ)*X 1 0+(4925512803/10000000000 : ℝ)*X 1 1+(3732755909/10000000000 : ℝ)*X 1 2+(2144987617/5000000000 : ℝ)*X 2 0+(4925512803/10000000000 : ℝ)*X 2 1+(3732755909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1416810363118404456724197/170312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3491621/100000000000000 : ℝ)*(base1) + (5111787/50000000000000 : ℝ)*(base16) + (164362119/12500000000000 : ℝ)*(base19) + (277215077/20000000000000 : ℝ)*(base23) + (129542509/50000000000000 : ℝ)*(upper3) + (1271005449795323/100000000000000 : ℝ)*(major0) + (1271005449795323/100000000000000 : ℝ)*(major1) + (1271005449795323/100000000000000 : ℝ)*(major2) + (215564674754687/12500000000000 : ℝ)*(sp0) + (862262799102353/50000000000000 : ℝ)*(sp1) + (1724525537249847/100000000000000 : ℝ)*(sp2) + (817479164566377/100000000000000 : ℝ)*(sp3) + (9528779357/100000000000000 : ℝ)*(sp4) + (4530911193/100000000000000 : ℝ)*(sp7) + (102185462371149/12500000000000 : ℝ)*(f.failure) + (107782932707827/6250000000000 : ℝ)*(f.sum) + (1690609866783/545000000000000000000000000 : ℝ)*base65 + (1329340094849851/340625000000000000000000000000 : ℝ)*base68 + (767531805031101/340625000000000000000000000000 : ℝ)*base70 + (1361988242377/665283203125000000000000000 : ℝ)*base71 + (1186985115249/272500000000000000000000000 : ℝ)*base73 + (394012019987351/340625000000000000000000000000 : ℝ)*base76 + (215515130715253/42578125000000000000000000000 : ℝ)*base77 + (191651803047619/85156250000000000000000000000 : ℝ)*base80 + (139684195471/272500000000000000000000000 : ℝ)*base82 + (8471177/1250000000000000000000 : ℝ)*base89 + (8471177/1250000000000000000000 : ℝ)*base91 + (8471177/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36481492472415371551485801/3746875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20587813/20000000000000 : ℝ)*(base1) + (986740239/50000000000000 : ℝ)*(base19) + (484100321/25000000000000 : ℝ)*(base23) + (227294253/100000000000000 : ℝ)*(upper3) + (216939369/100000000000000 : ℝ)*(upper5) + (162939526064159/12500000000000 : ℝ)*(major0) + (162939526064159/12500000000000 : ℝ)*(major1) + (162939526064159/12500000000000 : ℝ)*(major2) + (2061245667/20000000000000 : ℝ)*(sp1) + (5134742851/50000000000000 : ℝ)*(sp2) + (884319133613813/50000000000000 : ℝ)*(sp4) + (442156471144937/25000000000000 : ℝ)*(sp5) + (221078244800197/12500000000000 : ℝ)*(sp6) + (419196912624259/50000000000000 : ℝ)*(sp7) + (419196964093791/50000000000000 : ℝ)*(f.failure) + (884319082144281/50000000000000 : ℝ)*(f.sum) + (1019433687729/749375000000000000000000000 : ℝ)*base65 + (1349389692802707/170312500000000000000000000000 : ℝ)*base68 + (160310069608957/170312500000000000000000000000 : ℝ)*base70 + (739049854935211/340625000000000000000000000000 : ℝ)*base71 + (16773647387099/2997500000000000000000000000 : ℝ)*base74 + (297428416537709/85156250000000000000000000000 : ℝ)*base75 + (267661069231979/21289062500000000000000000000 : ℝ)*base78 + (92329731675729/21289062500000000000000000000 : ℝ)*base80 + (5801789602281/2997500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (12192557/5000000000000000000000 : ℝ)*base90 + (12192557/5000000000000000000000 : ℝ)*base92 + (12192557/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1361_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155477773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5347/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (389/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (883/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19321/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1361_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1361_s2_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-403714033/2000000000 : ℝ)*x 0 + (2737333163/5000000000 : ℝ)*x 1 + (3242611/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (403714033/2000000000 : ℝ)^4321 ≤ (245601279641/2000000000000 : ℝ)^3297 := by
    have hnat : (403714033 : ℕ)^4321*2000000000000^3297 ≤ 245601279641^3297*2000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403714033 2000000000 245601279641 2000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2737333163/5000000000 : ℝ)^4321 ≤ (45404130911489/100000000000000 : ℝ)^3297 := by
    have hnat : (2737333163 : ℕ)^4321*100000000000000^3297 ≤ 45404130911489^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737333163 5000000000 45404130911489 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3242611/6250000 : ℝ)^4321 ≤ (4231580509529/10000000000000 : ℝ)^3297 := by
    have hnat : (3242611 : ℕ)^4321*10000000000000^3297 ≤ 4231580509529^3297*6250000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3242611 6250000 4231580509529 10000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-403714033/2000000000 : ℝ), (2737333163/5000000000 : ℝ), (3242611/6250000 : ℝ)] ![(245601279641/2000000000000 : ℝ), (45404130911489/100000000000000 : ℝ), (4231580509529/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-403714033/2000000000 : ℝ)|^4321 ≤ (245601279641/2000000000000 : ℝ)^3297
        have hw : |(-403714033/2000000000 : ℝ)|=(403714033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2737333163/5000000000 : ℝ)|^4321 ≤ (45404130911489/100000000000000 : ℝ)^3297
        have hw : |(2737333163/5000000000 : ℝ)|=(2737333163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3242611/6250000 : ℝ)|^4321 ≤ (4231580509529/10000000000000 : ℝ)^3297
        have hw : |(3242611/6250000 : ℝ)|=(3242611/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s2_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167644759/312500000 : ℝ)*x 0 + (-433290041/2000000000 : ℝ)*x 1 + (324261121/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167644759/312500000 : ℝ)^4321 ≤ (8842376851561/20000000000000 : ℝ)^3297 := by
    have hnat : (167644759 : ℕ)^4321*20000000000000^3297 ≤ 8842376851561^3297*312500000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167644759 312500000 8842376851561 20000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (433290041/2000000000 : ℝ)^4321 ≤ (13472307041381/100000000000000 : ℝ)^3297 := by
    have hnat : (433290041 : ℕ)^4321*100000000000000^3297 ≤ 13472307041381^3297*2000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433290041 2000000000 13472307041381 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (324261121/625000000 : ℝ)^4321 ≤ (21157904343463/50000000000000 : ℝ)^3297 := by
    have hnat : (324261121 : ℕ)^4321*50000000000000^3297 ≤ 21157904343463^3297*625000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324261121 625000000 21157904343463 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167644759/312500000 : ℝ), (-433290041/2000000000 : ℝ), (324261121/625000000 : ℝ)] ![(8842376851561/20000000000000 : ℝ), (13472307041381/100000000000000 : ℝ), (21157904343463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167644759/312500000 : ℝ)|^4321 ≤ (8842376851561/20000000000000 : ℝ)^3297
        have hw : |(167644759/312500000 : ℝ)|=(167644759/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-433290041/2000000000 : ℝ)|^4321 ≤ (13472307041381/100000000000000 : ℝ)^3297
        have hw : |(-433290041/2000000000 : ℝ)|=(433290041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(324261121/625000000 : ℝ)|^4321 ≤ (21157904343463/50000000000000 : ℝ)^3297
        have hw : |(324261121/625000000 : ℝ)|=(324261121/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s2_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364632337/10000000000 : ℝ)*x 0 + (2594088937/5000000000 : ℝ)*x 1 + (-2166450221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364632337/10000000000 : ℝ)^4321 ≤ (8842376957411/20000000000000 : ℝ)^3297 := by
    have hnat : (5364632337 : ℕ)^4321*20000000000000^3297 ≤ 8842376957411^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364632337 10000000000 8842376957411 20000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2594088937/5000000000 : ℝ)^4321 ≤ (5289476003023/12500000000000 : ℝ)^3297 := by
    have hnat : (2594088937 : ℕ)^4321*12500000000000^3297 ≤ 5289476003023^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594088937 5000000000 5289476003023 12500000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2166450221/10000000000 : ℝ)^4321 ≤ (13472307171781/100000000000000 : ℝ)^3297 := by
    have hnat : (2166450221 : ℕ)^4321*100000000000000^3297 ≤ 13472307171781^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166450221 10000000000 13472307171781 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364632337/10000000000 : ℝ), (2594088937/5000000000 : ℝ), (-2166450221/10000000000 : ℝ)] ![(8842376957411/20000000000000 : ℝ), (5289476003023/12500000000000 : ℝ), (13472307171781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364632337/10000000000 : ℝ)|^4321 ≤ (8842376957411/20000000000000 : ℝ)^3297
        have hw : |(5364632337/10000000000 : ℝ)|=(5364632337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2594088937/5000000000 : ℝ)|^4321 ≤ (5289476003023/12500000000000 : ℝ)^3297
        have hw : |(2594088937/5000000000 : ℝ)|=(2594088937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2166450221/10000000000 : ℝ)|^4321 ≤ (13472307171781/100000000000000 : ℝ)^3297
        have hw : |(-2166450221/10000000000 : ℝ)|=(2166450221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s2_3 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2157956381/5000000000 : ℝ)*x 0 + (4023511109/10000000000 : ℝ)*x 1 + (4627874203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157956381/5000000000 : ℝ)^4321 ≤ (16622699904017/50000000000000 : ℝ)^3297 := by
    have hnat : (2157956381 : ℕ)^4321*50000000000000^3297 ≤ 16622699904017^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157956381 5000000000 16622699904017 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4023511109/10000000000 : ℝ)^4321 ≤ (15162519280211/50000000000000 : ℝ)^3297 := by
    have hnat : (4023511109 : ℕ)^4321*50000000000000^3297 ≤ 15162519280211^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023511109 10000000000 15162519280211 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4627874203/10000000000 : ℝ)^4321 ≤ (728591232357/2000000000000 : ℝ)^3297 := by
    have hnat : (4627874203 : ℕ)^4321*2000000000000^3297 ≤ 728591232357^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4627874203 10000000000 728591232357 2000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157956381/5000000000 : ℝ), (4023511109/10000000000 : ℝ), (4627874203/10000000000 : ℝ)] ![(16622699904017/50000000000000 : ℝ), (15162519280211/50000000000000 : ℝ), (728591232357/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157956381/5000000000 : ℝ)|^4321 ≤ (16622699904017/50000000000000 : ℝ)^3297
        have hw : |(2157956381/5000000000 : ℝ)|=(2157956381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4023511109/10000000000 : ℝ)|^4321 ≤ (15162519280211/50000000000000 : ℝ)^3297
        have hw : |(4023511109/10000000000 : ℝ)|=(4023511109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4627874203/10000000000 : ℝ)|^4321 ≤ (728591232357/2000000000000 : ℝ)^3297
        have hw : |(4627874203/10000000000 : ℝ)|=(4627874203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s2_4 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-50465771/250000000 : ℝ)*x 0 + (1297484423/2500000000 : ℝ)*x 1 + (1368222671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50465771/250000000 : ℝ)^4321 ≤ (1535068468307/12500000000000 : ℝ)^3297 := by
    have hnat : (50465771 : ℕ)^4321*12500000000000^3297 ≤ 1535068468307^3297*250000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50465771 250000000 1535068468307 12500000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1297484423/2500000000 : ℝ)^4321 ≤ (2116731020181/5000000000000 : ℝ)^3297 := by
    have hnat : (1297484423 : ℕ)^4321*5000000000000^3297 ≤ 2116731020181^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297484423 2500000000 2116731020181 5000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368222671/2500000000 : ℝ)^4321 ≤ (22692415916679/50000000000000 : ℝ)^3297 := by
    have hnat : (1368222671 : ℕ)^4321*50000000000000^3297 ≤ 22692415916679^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368222671 2500000000 22692415916679 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50465771/250000000 : ℝ), (1297484423/2500000000 : ℝ), (1368222671/2500000000 : ℝ)] ![(1535068468307/12500000000000 : ℝ), (2116731020181/5000000000000 : ℝ), (22692415916679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50465771/250000000 : ℝ)|^4321 ≤ (1535068468307/12500000000000 : ℝ)^3297
        have hw : |(-50465771/250000000 : ℝ)|=(50465771/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1297484423/2500000000 : ℝ)|^4321 ≤ (2116731020181/5000000000000 : ℝ)^3297
        have hw : |(1297484423/2500000000 : ℝ)|=(1297484423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1368222671/2500000000 : ℝ)|^4321 ≤ (22692415916679/50000000000000 : ℝ)^3297
        have hw : |(1368222671/2500000000 : ℝ)|=(1368222671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s2_5 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322659913/2500000000 : ℝ)*x 0 + (-940868587/5000000000 : ℝ)*x 1 + (5472890637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322659913/2500000000 : ℝ)^4321 ≤ (21707203140903/50000000000000 : ℝ)^3297 := by
    have hnat : (1322659913 : ℕ)^4321*50000000000000^3297 ≤ 21707203140903^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322659913 2500000000 21707203140903 50000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (940868587/5000000000 : ℝ)^4321 ≤ (448030495693/4000000000000 : ℝ)^3297 := by
    have hnat : (940868587 : ℕ)^4321*4000000000000^3297 ≤ 448030495693^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940868587 5000000000 448030495693 4000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5472890637/10000000000 : ℝ)^4321 ≤ (45384831322551/100000000000000 : ℝ)^3297 := by
    have hnat : (5472890637 : ℕ)^4321*100000000000000^3297 ≤ 45384831322551^3297*10000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472890637 10000000000 45384831322551 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322659913/2500000000 : ℝ), (-940868587/5000000000 : ℝ), (5472890637/10000000000 : ℝ)] ![(21707203140903/50000000000000 : ℝ), (448030495693/4000000000000 : ℝ), (45384831322551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322659913/2500000000 : ℝ)|^4321 ≤ (21707203140903/50000000000000 : ℝ)^3297
        have hw : |(1322659913/2500000000 : ℝ)|=(1322659913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-940868587/5000000000 : ℝ)|^4321 ≤ (448030495693/4000000000000 : ℝ)^3297
        have hw : |(-940868587/5000000000 : ℝ)|=(940868587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5472890637/10000000000 : ℝ)|^4321 ≤ (45384831322551/100000000000000 : ℝ)^3297
        have hw : |(5472890637/10000000000 : ℝ)|=(5472890637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s2_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2645319809/5000000000 : ℝ)*x 0 + (85513917/156250000 : ℝ)*x 1 + (-470434287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645319809/5000000000 : ℝ)^4321 ≤ (43414405916153/100000000000000 : ℝ)^3297 := by
    have hnat : (2645319809 : ℕ)^4321*100000000000000^3297 ≤ 43414405916153^3297*5000000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645319809 5000000000 43414405916153 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85513917/156250000 : ℝ)^4321 ≤ (45384831876831/100000000000000 : ℝ)^3297 := by
    have hnat : (85513917 : ℕ)^4321*100000000000000^3297 ≤ 45384831876831^3297*156250000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85513917 156250000 45384831876831 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (470434287/2500000000 : ℝ)^4321 ≤ (11200762189497/100000000000000 : ℝ)^3297 := by
    have hnat : (470434287 : ℕ)^4321*100000000000000^3297 ≤ 11200762189497^3297*2500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470434287 2500000000 11200762189497 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645319809/5000000000 : ℝ), (85513917/156250000 : ℝ), (-470434287/2500000000 : ℝ)] ![(43414405916153/100000000000000 : ℝ), (45384831876831/100000000000000 : ℝ), (11200762189497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645319809/5000000000 : ℝ)|^4321 ≤ (43414405916153/100000000000000 : ℝ)^3297
        have hw : |(2645319809/5000000000 : ℝ)|=(2645319809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85513917/156250000 : ℝ)|^4321 ≤ (45384831876831/100000000000000 : ℝ)^3297
        have hw : |(85513917/156250000 : ℝ)|=(85513917/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-470434287/2500000000 : ℝ)|^4321 ≤ (11200762189497/100000000000000 : ℝ)^3297
        have hw : |(-470434287/2500000000 : ℝ)|=(470434287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1361_s2_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53950513/125000000 : ℝ)*x 0 + (231208087/500000000 : ℝ)*x 1 + (100681409/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53950513/125000000 : ℝ)^4321 ≤ (33246694833791/100000000000000 : ℝ)^3297 := by
    have hnat : (53950513 : ℕ)^4321*100000000000000^3297 ≤ 33246694833791^3297*125000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53950513 125000000 33246694833791 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (231208087/500000000 : ℝ)^4321 ≤ (9097816573703/25000000000000 : ℝ)^3297 := by
    have hnat : (231208087 : ℕ)^4321*25000000000000^3297 ≤ 9097816573703^3297*500000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231208087 500000000 9097816573703 25000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100681409/250000000 : ℝ)^4321 ≤ (30362038853609/100000000000000 : ℝ)^3297 := by
    have hnat : (100681409 : ℕ)^4321*100000000000000^3297 ≤ 30362038853609^3297*250000000^4321 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100681409 250000000 30362038853609 100000000000000 4321 3297 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4321/1024 : ℝ)) 4321 3297 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53950513/125000000 : ℝ), (231208087/500000000 : ℝ), (100681409/250000000 : ℝ)] ![(33246694833791/100000000000000 : ℝ), (9097816573703/25000000000000 : ℝ), (30362038853609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53950513/125000000 : ℝ)|^4321 ≤ (33246694833791/100000000000000 : ℝ)^3297
        have hw : |(53950513/125000000 : ℝ)|=(53950513/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(231208087/500000000 : ℝ)|^4321 ≤ (9097816573703/25000000000000 : ℝ)^3297
        have hw : |(231208087/500000000 : ℝ)|=(231208087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(100681409/250000000 : ℝ)|^4321 ≤ (30362038853609/100000000000000 : ℝ)^3297
        have hw : |(100681409/250000000 : ℝ)|=(100681409/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1361_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155477773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19321/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (883/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (9973/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16031/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19321/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (883/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19321/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (883/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19321/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (883/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19321/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (883/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19321/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (883/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19321/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (883/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (883/12500 : ℝ) ^ (135/32 : ℝ) ≤ (174318152270573/12500000000000000000 : ℝ) := by
    have hpowers : (883/12500 : ℝ)^135 ≤ (174318152270573/12500000000000000000 : ℝ)^32 := by
      have hnat : (883 : ℕ)^135*12500000000000000000^32 ≤ 174318152270573^32*12500^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        883 12500 174318152270573 12500000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (883/12500 : ℝ)) (X := (174318152270573/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hpowhi : (19321/100000 : ℝ) ^ (135/32 : ℝ) ≤ (3039396778542239/3125000000000000000 : ℝ) := by
    have hpowers : (19321/100000 : ℝ)^135 ≤ (3039396778542239/3125000000000000000 : ℝ)^32 := by
      have hnat : (19321 : ℕ)^135*3125000000000000000^32 ≤ 3039396778542239^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19321 100000 3039396778542239 3125000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19321/100000 : ℝ)) (X := (3039396778542239/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250174318152270573/6250000000000000000 : ℝ) ≤ (10000066111069897/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (6250174318152270573/6250000000000000000 : ℝ)^32 ≤ (10000066111069897/10000000000000000 : ℝ)^135 := by
      have hnat : (6250174318152270573 : ℕ)^32*10000000000000000^135 ≤ 10000066111069897^135*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250174318152270573 6250000000000000000 10000066111069897 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000066111069897/10000000000000000 : ℝ)) (X := (6250174318152270573/6250000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (12512331905266439529/12500000000000000000 : ℝ) ≤ (250058440376057/250000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (12512331905266439529/12500000000000000000 : ℝ)^32 ≤ (250058440376057/250000000000000 : ℝ)^135 := by
      have hnat : (12512331905266439529 : ℕ)^32*250000000000000^135 ≤ 250058440376057^135*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12512331905266439529 12500000000000000000 250058440376057 250000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250058440376057/250000000000000 : ℝ)) (X := (12512331905266439529/12500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (1565539396778542239/1562500000000000000 : ℝ) ≤ (10004609119014663/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (1565539396778542239/1562500000000000000 : ℝ)^32 ≤ (10004609119014663/10000000000000000 : ℝ)^135 := by
      have hnat : (1565539396778542239 : ℕ)^32*10000000000000000^135 ≤ 10004609119014663^135*1562500000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1565539396778542239 1562500000000000000 10004609119014663 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004609119014663/10000000000000000 : ℝ)) (X := (1565539396778542239/1562500000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(174318152270573/12500000000000000000 : ℝ) ≤ ((24507743703052380101/24514000000000000000 : ℝ)+2*(2271503972383/1225700000000000 : ℝ)*(883/12500 : ℝ))^(135/32 : ℝ) := by
    rw [show (24507743703052380101/24514000000000000000 : ℝ)+2*(2271503972383/1225700000000000 : ℝ)*(883/12500 : ℝ)=(10000066111069897/10000000000000000 : ℝ) by norm_num, show 1+2*(174318152270573/12500000000000000000 : ℝ)=(6250174318152270573/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3039396778542239/3125000000000000000 : ℝ)+(174318152270573/12500000000000000000 : ℝ) ≤ ((24507743703052380101/24514000000000000000 : ℝ)+(2271503972383/1225700000000000 : ℝ)*((19321/100000 : ℝ)+(883/12500 : ℝ)))^(135/32 : ℝ) := by
    rw [show (24507743703052380101/24514000000000000000 : ℝ)+(2271503972383/1225700000000000 : ℝ)*((19321/100000 : ℝ)+(883/12500 : ℝ))=(250058440376057/250000000000000 : ℝ) by norm_num, show 1+(3039396778542239/3125000000000000000 : ℝ)+(174318152270573/12500000000000000000 : ℝ)=(12512331905266439529/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3039396778542239/3125000000000000000 : ℝ) ≤ ((24507743703052380101/24514000000000000000 : ℝ)+2*(2271503972383/1225700000000000 : ℝ)*(19321/100000 : ℝ))^(135/32 : ℝ) := by
    rw [show (24507743703052380101/24514000000000000000 : ℝ)+2*(2271503972383/1225700000000000 : ℝ)*(19321/100000 : ℝ)=(10004609119014663/10000000000000000 : ℝ) by norm_num, show 1+2*(3039396778542239/3125000000000000000 : ℝ)=(1565539396778542239/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24507743703052380101/24514000000000000000 : ℝ)*(X 1 0+X 2 0)+(2271503972383/1225700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (883/12500 : ℝ)) (hi := (19321/100000 : ℝ)) (c := (24507743703052380101/24514000000000000000 : ℝ)) (alpha := (2271503972383/1225700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24507743703052380101/24514000000000000000 : ℝ)*(X 0 1+X 2 1)+(2271503972383/1225700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (883/12500 : ℝ)) (hi := (19321/100000 : ℝ)) (c := (24507743703052380101/24514000000000000000 : ℝ)) (alpha := (2271503972383/1225700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24507743703052380101/24514000000000000000 : ℝ)*(X 0 2+X 1 2)+(2271503972383/1225700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (135/32 : ℝ)) (lo := (883/12500 : ℝ)) (hi := (19321/100000 : ℝ)) (c := (24507743703052380101/24514000000000000000 : ℝ)) (alpha := (2271503972383/1225700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-403714033/2000000000 : ℝ)*X 0 0+(2737333163/5000000000 : ℝ)*X 0 1+(3242611/6250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167644759/312500000 : ℝ)*X 1 0+(-433290041/2000000000 : ℝ)*X 1 1+(324261121/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5364632337/10000000000 : ℝ)*X 2 0+(2594088937/5000000000 : ℝ)*X 2 1+(-2166450221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2157956381/5000000000 : ℝ)*X 0 0+(4023511109/10000000000 : ℝ)*X 0 1+(4627874203/10000000000 : ℝ)*X 0 2+(2157956381/5000000000 : ℝ)*X 1 0+(4023511109/10000000000 : ℝ)*X 1 1+(4627874203/10000000000 : ℝ)*X 1 2+(2157956381/5000000000 : ℝ)*X 2 0+(4023511109/10000000000 : ℝ)*X 2 1+(4627874203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-50465771/250000000 : ℝ)*X 0 0+(1297484423/2500000000 : ℝ)*X 0 1+(1368222671/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322659913/2500000000 : ℝ)*X 1 0+(-940868587/5000000000 : ℝ)*X 1 1+(5472890637/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2645319809/5000000000 : ℝ)*X 2 0+(85513917/156250000 : ℝ)*X 2 1+(-470434287/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((53950513/125000000 : ℝ)*X 0 0+(231208087/500000000 : ℝ)*X 0 1+(100681409/250000000 : ℝ)*X 0 2+(53950513/125000000 : ℝ)*X 1 0+(231208087/500000000 : ℝ)*X 1 1+(100681409/250000000 : ℝ)*X 1 2+(53950513/125000000 : ℝ)*X 2 0+(231208087/500000000 : ℝ)*X 2 1+(100681409/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1361_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (866926607715293981536833/85000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55712109/3125000000000 : ℝ)*(base19) + (868767999/50000000000000 : ℝ)*(base23) + (20689823/50000000000000 : ℝ)*(lower2) + (245353489/100000000000000 : ℝ)*(upper3) + (176089793/100000000000000 : ℝ)*(upper5) + (128631201292477/5000000000000 : ℝ)*(major0) + (128631201292477/5000000000000 : ℝ)*(major1) + (128631201292477/5000000000000 : ℝ)*(major2) + (3490564969469049/100000000000000 : ℝ)*(sp0) + (1745294409330169/50000000000000 : ℝ)*(sp1) + (3490588863911829/100000000000000 : ℝ)*(sp2) + (413661316235659/25000000000000 : ℝ)*(sp3) + (12815989389/50000000000000 : ℝ)*(sp4) + (11845337391/100000000000000 : ℝ)*(sp7) + (1654657110280027/100000000000000 : ℝ)*(f.failure) + (3490590601447827/100000000000000 : ℝ)*(f.sum) + (1405654901069/2451400000000000000000000000 : ℝ)*base65 + (1819579825746359823/122570000000000000000000000000000 : ℝ)*base68 + (1709361744689779823/122570000000000000000000000000000 : ℝ)*base70 + (621082104773499823/122570000000000000000000000000000 : ℝ)*base72 + (5970842345677/6128500000000000000000000000 : ℝ)*base74 + (504853584856899823/122570000000000000000000000000000 : ℝ)*base76 + (1115090810298029823/122570000000000000000000000000000 : ℝ)*base78 + (1471337275160079823/122570000000000000000000000000000 : ℝ)*base80 + (22314995653599/12257000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4339871/10000000000000000000000 : ℝ)*base89 + (4339871/10000000000000000000000 : ℝ)*base91 + (4339871/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20185440909118740811173/2451400000000000000000000000 : ℝ) := by norm_num
    linear_combination (1690491119/100000000000000 : ℝ)*(base19) + (1849913227/100000000000000 : ℝ)*(base23) + (193106819/100000000000000 : ℝ)*(upper3) + (74853669/100000000000000 : ℝ)*(lower4) + (17721943/12500000000000 : ℝ)*(upper5) + (520946167620381/20000000000000 : ℝ)*(major0) + (520946167620381/20000000000000 : ℝ)*(major1) + (520946167620381/20000000000000 : ℝ)*(major2) + (609810427/3125000000000 : ℝ)*(sp1) + (5605135253/25000000000000 : ℝ)*(sp2) + (706830774402797/20000000000000 : ℝ)*(sp4) + (1767066333794601/50000000000000 : ℝ)*(sp5) + (1767064800779873/50000000000000 : ℝ)*(sp6) + (1675307529714813/100000000000000 : ℝ)*(sp7) + (1675307529714813/100000000000000 : ℝ)*(f.failure) + (706830774402797/20000000000000 : ℝ)*(f.sum) + (56026193928917/12257000000000000000000000000 : ℝ)*base66 + (1814687048982301519/490280000000000000000000000000000 : ℝ)*base68 + (1121087530952701519/490280000000000000000000000000000 : ℝ)*base70 + (1048933041002781519/490280000000000000000000000000000 : ℝ)*base72 + (42796358682541/12257000000000000000000000000 : ℝ)*base74 + (3636431013864658481/490280000000000000000000000000000 : ℝ)*base75 + (1079499354839138481/490280000000000000000000000000000 : ℝ)*base77 + (2585874474665218481/490280000000000000000000000000000 : ℝ)*base79 + (20385589625417/12257000000000000000000000000 : ℝ)*base82 + (49648551/10000000000000000000000 : ℝ)*base90 + (49648551/10000000000000000000000 : ℝ)*base92 + (49648551/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1361_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155477773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19321/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (883/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9973/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16031/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1361_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1361_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155477773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9973/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16031/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1361_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1361_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1361_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (4321/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155477773/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9973/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16031/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1361_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

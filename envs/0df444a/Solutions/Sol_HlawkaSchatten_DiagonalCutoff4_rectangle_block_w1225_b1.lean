-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1225_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:12:28.752677+00:00
-- url     : https://prove2.me/submissions/c626d609-ce1e-4a6d-9436-de340cd53c05

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
theorem support_rectangle_w1225_s3_0 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-8300097/39062500 : ℝ)*x 0 + (1355291853/2500000000 : ℝ)*x 1 + (2619644803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8300097/39062500 : ℝ)^4209 ≤ (12913761711663/100000000000000 : ℝ)^3185 := by
    have hnat : (8300097 : ℕ)^4209*100000000000000^3185 ≤ 12913761711663^3185*39062500^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8300097 39062500 12913761711663 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355291853/2500000000 : ℝ)^4209 ≤ (22262389979233/50000000000000 : ℝ)^3185 := by
    have hnat : (1355291853 : ℕ)^4209*50000000000000^3185 ≤ 22262389979233^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355291853 2500000000 22262389979233 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619644803/5000000000 : ℝ)^4209 ≤ (42561458321877/100000000000000 : ℝ)^3185 := by
    have hnat : (2619644803 : ℕ)^4209*100000000000000^3185 ≤ 42561458321877^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619644803 5000000000 42561458321877 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8300097/39062500 : ℝ), (1355291853/2500000000 : ℝ), (2619644803/5000000000 : ℝ)] ![(12913761711663/100000000000000 : ℝ), (22262389979233/50000000000000 : ℝ), (42561458321877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8300097/39062500 : ℝ)|^4209 ≤ (12913761711663/100000000000000 : ℝ)^3185
        have hw : |(-8300097/39062500 : ℝ)|=(8300097/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355291853/2500000000 : ℝ)|^4209 ≤ (22262389979233/50000000000000 : ℝ)^3185
        have hw : |(1355291853/2500000000 : ℝ)|=(1355291853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619644803/5000000000 : ℝ)|^4209 ≤ (42561458321877/100000000000000 : ℝ)^3185
        have hw : |(2619644803/5000000000 : ℝ)|=(2619644803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s3_1 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535186771/1000000000 : ℝ)*x 0 + (-2217637097/10000000000 : ℝ)*x 1 + (5239289591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535186771/1000000000 : ℝ)^4209 ≤ (8754834162321/20000000000000 : ℝ)^3185 := by
    have hnat : (535186771 : ℕ)^4209*20000000000000^3185 ≤ 8754834162321^3185*1000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535186771 1000000000 8754834162321 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217637097/10000000000 : ℝ)^4209 ≤ (6832185511657/50000000000000 : ℝ)^3185 := by
    have hnat : (2217637097 : ℕ)^4209*50000000000000^3185 ≤ 6832185511657^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217637097 10000000000 6832185511657 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239289591/10000000000 : ℝ)^4209 ≤ (2660091135053/6250000000000 : ℝ)^3185 := by
    have hnat : (5239289591 : ℕ)^4209*6250000000000^3185 ≤ 2660091135053^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239289591 10000000000 2660091135053 6250000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535186771/1000000000 : ℝ), (-2217637097/10000000000 : ℝ), (5239289591/10000000000 : ℝ)] ![(8754834162321/20000000000000 : ℝ), (6832185511657/50000000000000 : ℝ), (2660091135053/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535186771/1000000000 : ℝ)|^4209 ≤ (8754834162321/20000000000000 : ℝ)^3185
        have hw : |(535186771/1000000000 : ℝ)|=(535186771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2217637097/10000000000 : ℝ)|^4209 ≤ (6832185511657/50000000000000 : ℝ)^3185
        have hw : |(-2217637097/10000000000 : ℝ)|=(2217637097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239289591/10000000000 : ℝ)|^4209 ≤ (2660091135053/6250000000000 : ℝ)^3185
        have hw : |(5239289591/10000000000 : ℝ)|=(5239289591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s3_2 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351867701/10000000000 : ℝ)*x 0 + (5239289711/10000000000 : ℝ)*x 1 + (-2217636949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351867701/10000000000 : ℝ)^4209 ≤ (10943542678581/25000000000000 : ℝ)^3185 := by
    have hnat : (5351867701 : ℕ)^4209*25000000000000^3185 ≤ 10943542678581^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351867701 10000000000 10943542678581 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239289711/10000000000 : ℝ)^4209 ≤ (21280729724541/50000000000000 : ℝ)^3185 := by
    have hnat : (5239289711 : ℕ)^4209*50000000000000^3185 ≤ 21280729724541^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239289711 10000000000 21280729724541 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2217636949/10000000000 : ℝ)^4209 ≤ (13664369818193/100000000000000 : ℝ)^3185 := by
    have hnat : (2217636949 : ℕ)^4209*100000000000000^3185 ≤ 13664369818193^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217636949 10000000000 13664369818193 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351867701/10000000000 : ℝ), (5239289711/10000000000 : ℝ), (-2217636949/10000000000 : ℝ)] ![(10943542678581/25000000000000 : ℝ), (21280729724541/50000000000000 : ℝ), (13664369818193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351867701/10000000000 : ℝ)|^4209 ≤ (10943542678581/25000000000000 : ℝ)^3185
        have hw : |(5351867701/10000000000 : ℝ)|=(5351867701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239289711/10000000000 : ℝ)|^4209 ≤ (21280729724541/50000000000000 : ℝ)^3185
        have hw : |(5239289711/10000000000 : ℝ)|=(5239289711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2217636949/10000000000 : ℝ)|^4209 ≤ (13664369818193/100000000000000 : ℝ)^3185
        have hw : |(-2217636949/10000000000 : ℝ)|=(2217636949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s3_3 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4351327293/10000000000 : ℝ)*x 0 + (4171244519/10000000000 : ℝ)*x 1 + (2269492721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351327293/10000000000 : ℝ)^4209 ≤ (1664968782507/5000000000000 : ℝ)^3185 := by
    have hnat : (4351327293 : ℕ)^4209*5000000000000^3185 ≤ 1664968782507^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351327293 10000000000 1664968782507 5000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171244519/10000000000 : ℝ)^4209 ≤ (31490414166211/100000000000000 : ℝ)^3185 := by
    have hnat : (4171244519 : ℕ)^4209*100000000000000^3185 ≤ 31490414166211^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171244519 10000000000 31490414166211 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2269492721/5000000000 : ℝ)^4209 ≤ (17605105084857/50000000000000 : ℝ)^3185 := by
    have hnat : (2269492721 : ℕ)^4209*50000000000000^3185 ≤ 17605105084857^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269492721 5000000000 17605105084857 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351327293/10000000000 : ℝ), (4171244519/10000000000 : ℝ), (2269492721/5000000000 : ℝ)] ![(1664968782507/5000000000000 : ℝ), (31490414166211/100000000000000 : ℝ), (17605105084857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351327293/10000000000 : ℝ)|^4209 ≤ (1664968782507/5000000000000 : ℝ)^3185
        have hw : |(4351327293/10000000000 : ℝ)|=(4351327293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171244519/10000000000 : ℝ)|^4209 ≤ (31490414166211/100000000000000 : ℝ)^3185
        have hw : |(4171244519/10000000000 : ℝ)|=(4171244519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2269492721/5000000000 : ℝ)|^4209 ≤ (17605105084857/50000000000000 : ℝ)^3185
        have hw : |(2269492721/5000000000 : ℝ)|=(2269492721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s3_4 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2124839669/10000000000 : ℝ)*x 0 + (5239957937/10000000000 : ℝ)*x 1 + (5420495367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124839669/10000000000 : ℝ)^4209 ≤ (12913880875837/100000000000000 : ℝ)^3185 := by
    have hnat : (2124839669 : ℕ)^4209*100000000000000^3185 ≤ 12913880875837^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124839669 10000000000 12913880875837 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239957937/10000000000 : ℝ)^4209 ≤ (42568633192849/100000000000000 : ℝ)^3185 := by
    have hnat : (5239957937 : ℕ)^4209*100000000000000^3185 ≤ 42568633192849^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239957937 10000000000 42568633192849 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420495367/10000000000 : ℝ)^4209 ≤ (2782342869893/6250000000000 : ℝ)^3185 := by
    have hnat : (5420495367 : ℕ)^4209*6250000000000^3185 ≤ 2782342869893^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420495367 10000000000 2782342869893 6250000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2124839669/10000000000 : ℝ), (5239957937/10000000000 : ℝ), (5420495367/10000000000 : ℝ)] ![(12913880875837/100000000000000 : ℝ), (42568633192849/100000000000000 : ℝ), (2782342869893/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2124839669/10000000000 : ℝ)|^4209 ≤ (12913880875837/100000000000000 : ℝ)^3185
        have hw : |(-2124839669/10000000000 : ℝ)|=(2124839669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239957937/10000000000 : ℝ)|^4209 ≤ (42568633192849/100000000000000 : ℝ)^3185
        have hw : |(5239957937/10000000000 : ℝ)|=(5239957937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420495367/10000000000 : ℝ)|^4209 ≤ (2782342869893/6250000000000 : ℝ)^3185
        have hw : |(5420495367/10000000000 : ℝ)|=(5420495367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s3_5 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305518553/10000000000 : ℝ)*x 0 + (-1018215907/5000000000 : ℝ)*x 1 + (2710247971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305518553/10000000000 : ℝ)^4209 ≤ (21636942804639/50000000000000 : ℝ)^3185 := by
    have hnat : (5305518553 : ℕ)^4209*50000000000000^3185 ≤ 21636942804639^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305518553 10000000000 21636942804639 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018215907/5000000000 : ℝ)^4209 ≤ (12208622211881/100000000000000 : ℝ)^3185 := by
    have hnat : (1018215907 : ℕ)^4209*100000000000000^3185 ≤ 12208622211881^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018215907 5000000000 12208622211881 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710247971/5000000000 : ℝ)^4209 ≤ (22258746079463/50000000000000 : ℝ)^3185 := by
    have hnat : (2710247971 : ℕ)^4209*50000000000000^3185 ≤ 22258746079463^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710247971 5000000000 22258746079463 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305518553/10000000000 : ℝ), (-1018215907/5000000000 : ℝ), (2710247971/5000000000 : ℝ)] ![(21636942804639/50000000000000 : ℝ), (12208622211881/100000000000000 : ℝ), (22258746079463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305518553/10000000000 : ℝ)|^4209 ≤ (21636942804639/50000000000000 : ℝ)^3185
        have hw : |(5305518553/10000000000 : ℝ)|=(5305518553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1018215907/5000000000 : ℝ)|^4209 ≤ (12208622211881/100000000000000 : ℝ)^3185
        have hw : |(-1018215907/5000000000 : ℝ)|=(1018215907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710247971/5000000000 : ℝ)|^4209 ≤ (22258746079463/50000000000000 : ℝ)^3185
        have hw : |(2710247971/5000000000 : ℝ)|=(2710247971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s3_6 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652760191/5000000000 : ℝ)*x 0 + (1355123827/2500000000 : ℝ)*x 1 + (-407286039/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652760191/5000000000 : ℝ)^4209 ≤ (21636952661787/50000000000000 : ℝ)^3185 := by
    have hnat : (2652760191 : ℕ)^4209*50000000000000^3185 ≤ 21636952661787^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652760191 5000000000 21636952661787 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355123827/2500000000 : ℝ)^4209 ≤ (8903497055589/20000000000000 : ℝ)^3185 := by
    have hnat : (1355123827 : ℕ)^4209*20000000000000^3185 ≤ 8903497055589^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355123827 2500000000 8903497055589 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407286039/2000000000 : ℝ)^4209 ≤ (12208609385237/100000000000000 : ℝ)^3185 := by
    have hnat : (407286039 : ℕ)^4209*100000000000000^3185 ≤ 12208609385237^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407286039 2000000000 12208609385237 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652760191/5000000000 : ℝ), (1355123827/2500000000 : ℝ), (-407286039/2000000000 : ℝ)] ![(21636952661787/50000000000000 : ℝ), (8903497055589/20000000000000 : ℝ), (12208609385237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652760191/5000000000 : ℝ)|^4209 ≤ (21636952661787/50000000000000 : ℝ)^3185
        have hw : |(2652760191/5000000000 : ℝ)|=(2652760191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355123827/2500000000 : ℝ)|^4209 ≤ (8903497055589/20000000000000 : ℝ)^3185
        have hw : |(1355123827/2500000000 : ℝ)|=(1355123827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-407286039/2000000000 : ℝ)|^4209 ≤ (12208609385237/100000000000000 : ℝ)^3185
        have hw : |(-407286039/2000000000 : ℝ)|=(407286039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s3_7 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1087839199/2500000000 : ℝ)*x 0 + (4537635517/10000000000 : ℝ)*x 1 + (1043150393/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087839199/2500000000 : ℝ)^4209 ≤ (33299674016929/100000000000000 : ℝ)^3185 := by
    have hnat : (1087839199 : ℕ)^4209*100000000000000^3185 ≤ 33299674016929^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087839199 2500000000 33299674016929 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4537635517/10000000000 : ℝ)^4209 ≤ (137485829427/390625000000 : ℝ)^3185 := by
    have hnat : (4537635517 : ℕ)^4209*390625000000^3185 ≤ 137485829427^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537635517 10000000000 137485829427 390625000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043150393/2500000000 : ℝ)^4209 ≤ (630079072767/2000000000000 : ℝ)^3185 := by
    have hnat : (1043150393 : ℕ)^4209*2000000000000^3185 ≤ 630079072767^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043150393 2500000000 630079072767 2000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087839199/2500000000 : ℝ), (4537635517/10000000000 : ℝ), (1043150393/2500000000 : ℝ)] ![(33299674016929/100000000000000 : ℝ), (137485829427/390625000000 : ℝ), (630079072767/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087839199/2500000000 : ℝ)|^4209 ≤ (33299674016929/100000000000000 : ℝ)^3185
        have hw : |(1087839199/2500000000 : ℝ)|=(1087839199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4537635517/10000000000 : ℝ)|^4209 ≤ (137485829427/390625000000 : ℝ)^3185
        have hw : |(4537635517/10000000000 : ℝ)|=(4537635517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043150393/2500000000 : ℝ)|^4209 ≤ (630079072767/2000000000000 : ℝ)^3185
        have hw : |(1043150393/2500000000 : ℝ)|=(1043150393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1225_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (943/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10867/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14717/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4067/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (943/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4067/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (943/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4067/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (943/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4067/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (943/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4067/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (943/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4067/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (943/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (943/10000 : ℝ) ^ (8417/2048 : ℝ) ≤ (3050375225033569/50000000000000000000 : ℝ) := by
    have hpowers : (943/10000 : ℝ)^8417 ≤ (3050375225033569/50000000000000000000 : ℝ)^2048 := by
      have hnat : (943 : ℕ)^8417*50000000000000000000^2048 ≤ 3050375225033569^2048*10000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        943 10000 3050375225033569 50000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (943/10000 : ℝ)) (X := (3050375225033569/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4067/25000 : ℝ) ^ (8417/2048 : ℝ) ≤ (2868542195904483/5000000000000000000 : ℝ) := by
    have hpowers : (4067/25000 : ℝ)^8417 ≤ (2868542195904483/5000000000000000000 : ℝ)^2048 := by
      have hnat : (4067 : ℕ)^8417*5000000000000000000^2048 ≤ 2868542195904483^2048*25000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4067 25000 2868542195904483 5000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4067/25000 : ℝ)) (X := (2868542195904483/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003050375225033569/25000000000000000000 : ℝ) ≤ (10000296869672869/10000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (25003050375225033569/25000000000000000000 : ℝ)^2048 ≤ (10000296869672869/10000000000000000 : ℝ)^8417 := by
      have hnat : (25003050375225033569 : ℕ)^2048*10000000000000000^8417 ≤ 10000296869672869^8417*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003050375225033569 25000000000000000000 10000296869672869 10000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000296869672869/10000000000000000 : ℝ)) (X := (25003050375225033569/25000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50031735797184078399/50000000000000000000 : ℝ) ≤ (10001544001677443/10000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (50031735797184078399/50000000000000000000 : ℝ)^2048 ≤ (10001544001677443/10000000000000000 : ℝ)^8417 := by
      have hnat : (50031735797184078399 : ℕ)^2048*10000000000000000^8417 ≤ 10001544001677443^8417*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031735797184078399 50000000000000000000 10001544001677443 10000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001544001677443/10000000000000000 : ℝ)) (X := (50031735797184078399/50000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2502868542195904483/2500000000000000000 : ℝ) ≤ (10002791133682017/10000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (2502868542195904483/2500000000000000000 : ℝ)^2048 ≤ (10002791133682017/10000000000000000 : ℝ)^8417 := by
      have hnat : (2502868542195904483 : ℕ)^2048*10000000000000000^8417 ≤ 10002791133682017^8417*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502868542195904483 2500000000000000000 10002791133682017 10000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002791133682017/10000000000000000 : ℝ)) (X := (2502868542195904483/2500000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3050375225033569/50000000000000000000 : ℝ) ≤ ((34179254542608406291/34190000000000000000 : ℝ)+2*(623566002287/341900000000000 : ℝ)*(943/10000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (34179254542608406291/34190000000000000000 : ℝ)+2*(623566002287/341900000000000 : ℝ)*(943/10000 : ℝ)=(10000296869672869/10000000000000000 : ℝ) by norm_num, show 1+2*(3050375225033569/50000000000000000000 : ℝ)=(25003050375225033569/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2868542195904483/5000000000000000000 : ℝ)+(3050375225033569/50000000000000000000 : ℝ) ≤ ((34179254542608406291/34190000000000000000 : ℝ)+(623566002287/341900000000000 : ℝ)*((4067/25000 : ℝ)+(943/10000 : ℝ)))^(8417/2048 : ℝ) := by
    rw [show (34179254542608406291/34190000000000000000 : ℝ)+(623566002287/341900000000000 : ℝ)*((4067/25000 : ℝ)+(943/10000 : ℝ))=(10001544001677443/10000000000000000 : ℝ) by norm_num, show 1+(2868542195904483/5000000000000000000 : ℝ)+(3050375225033569/50000000000000000000 : ℝ)=(50031735797184078399/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2868542195904483/5000000000000000000 : ℝ) ≤ ((34179254542608406291/34190000000000000000 : ℝ)+2*(623566002287/341900000000000 : ℝ)*(4067/25000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (34179254542608406291/34190000000000000000 : ℝ)+2*(623566002287/341900000000000 : ℝ)*(4067/25000 : ℝ)=(10002791133682017/10000000000000000 : ℝ) by norm_num, show 1+2*(2868542195904483/5000000000000000000 : ℝ)=(2502868542195904483/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34179254542608406291/34190000000000000000 : ℝ)*(X 1 0+X 2 0)+(623566002287/341900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (943/10000 : ℝ)) (hi := (4067/25000 : ℝ)) (c := (34179254542608406291/34190000000000000000 : ℝ)) (alpha := (623566002287/341900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34179254542608406291/34190000000000000000 : ℝ)*(X 0 1+X 2 1)+(623566002287/341900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (943/10000 : ℝ)) (hi := (4067/25000 : ℝ)) (c := (34179254542608406291/34190000000000000000 : ℝ)) (alpha := (623566002287/341900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34179254542608406291/34190000000000000000 : ℝ)*(X 0 2+X 1 2)+(623566002287/341900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (943/10000 : ℝ)) (hi := (4067/25000 : ℝ)) (c := (34179254542608406291/34190000000000000000 : ℝ)) (alpha := (623566002287/341900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-8300097/39062500 : ℝ)*X 0 0+(1355291853/2500000000 : ℝ)*X 0 1+(2619644803/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535186771/1000000000 : ℝ)*X 1 0+(-2217637097/10000000000 : ℝ)*X 1 1+(5239289591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351867701/10000000000 : ℝ)*X 2 0+(5239289711/10000000000 : ℝ)*X 2 1+(-2217636949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351327293/10000000000 : ℝ)*X 0 0+(4171244519/10000000000 : ℝ)*X 0 1+(2269492721/5000000000 : ℝ)*X 0 2+(4351327293/10000000000 : ℝ)*X 1 0+(4171244519/10000000000 : ℝ)*X 1 1+(2269492721/5000000000 : ℝ)*X 1 2+(4351327293/10000000000 : ℝ)*X 2 0+(4171244519/10000000000 : ℝ)*X 2 1+(2269492721/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2124839669/10000000000 : ℝ)*X 0 0+(5239957937/10000000000 : ℝ)*X 0 1+(5420495367/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305518553/10000000000 : ℝ)*X 1 0+(-1018215907/5000000000 : ℝ)*X 1 1+(2710247971/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652760191/5000000000 : ℝ)*X 2 0+(1355123827/2500000000 : ℝ)*X 2 1+(-407286039/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087839199/2500000000 : ℝ)*X 0 0+(4537635517/10000000000 : ℝ)*X 0 1+(1043150393/2500000000 : ℝ)*X 0 2+(1087839199/2500000000 : ℝ)*X 1 0+(4537635517/10000000000 : ℝ)*X 1 1+(1043150393/2500000000 : ℝ)*X 1 2+(1087839199/2500000000 : ℝ)*X 2 0+(4537635517/10000000000 : ℝ)*X 2 1+(1043150393/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2958726299894326237019413173/427375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (631019701/50000000000000 : ℝ)*(base19) + (550929629/50000000000000 : ℝ)*(base23) + (5048617/6250000000000 : ℝ)*(lower2) + (44110239/50000000000000 : ℝ)*(upper3) + (139803057/100000000000000 : ℝ)*(upper5) + (2054394600934101/50000000000000 : ℝ)*(major0) + (2054394600934101/50000000000000 : ℝ)*(major1) + (2054394600934101/50000000000000 : ℝ)*(major2) + (687277648321563/12500000000000 : ℝ)*(sp0) + (549824775767473/10000000000000 : ℝ)*(sp1) + (2749123958927437/50000000000000 : ℝ)*(sp2) + (1359658738918891/50000000000000 : ℝ)*(sp3) + (6958285407/25000000000000 : ℝ)*(sp4) + (11675417099/100000000000000 : ℝ)*(sp7) + (2719329153254881/100000000000000 : ℝ)*(f.failure) + (1374562254928533/25000000000000 : ℝ)*(f.sum) + (20900855908331/4273750000000000000000000000 : ℝ)*base65 + (17179900499763970609/1709500000000000000000000000000000 : ℝ)*base68 + (28587423141610470609/1709500000000000000000000000000000 : ℝ)*base70 + (6071473947261470609/1709500000000000000000000000000000 : ℝ)*base72 + (68756676644029/17095000000000000000000000000 : ℝ)*base73 + (16024828235645470609/1709500000000000000000000000000000 : ℝ)*base76 + (12397867681385529391/1709500000000000000000000000000000 : ℝ)*base77 + (31874181833898970609/1709500000000000000000000000000000 : ℝ)*base80 + (13299107809849/4273750000000000000000000000 : ℝ)*base82 + (24268163/2500000000000000000000 : ℝ)*base89 + (24268163/2500000000000000000000 : ℝ)*base91 + (24268163/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42041640844134298597449/4273750000000000000000000000 : ℝ) := by norm_num
    linear_combination (881846393/100000000000000 : ℝ)*(base19) + (700682583/20000000000000 : ℝ)*(base23) + (1370527/4000000000000 : ℝ)*(upper2) + (245905341/50000000000000 : ℝ)*(upper3) + (2069627658007773/50000000000000 : ℝ)*(major0) + (2069627658007773/50000000000000 : ℝ)*(major1) + (2069627658007773/50000000000000 : ℝ)*(major2) + (12721670479/100000000000000 : ℝ)*(sp1) + (86842559701/100000000000000 : ℝ)*(sp2) + (546266989/20000000000000 : ℝ)*(sp3) + (692377211794831/12500000000000 : ℝ)*(sp4) + (221560163633671/4000000000000 : ℝ)*(sp5) + (346182959274127/6250000000000 : ℝ)*(sp6) + (54789797568631/2000000000000 : ℝ)*(sp7) + (85609144055203/3125000000000 : ℝ)*(f.failure) + (692377211794831/12500000000000 : ℝ)*(f.sum) + (19713981103733/17095000000000000000000000000 : ℝ)*base66 + (370086315285699943/1709500000000000000000000000000000 : ℝ)*base67 + (1276647896401800057/1709500000000000000000000000000000 : ℝ)*base70 + (184450473019800057/1709500000000000000000000000000000 : ℝ)*base72 + (14977528641481/8547500000000000000000000000 : ℝ)*base73 + (2163075819929699943/1709500000000000000000000000000000 : ℝ)*base75 + (8827574706139800057/1709500000000000000000000000000000 : ℝ)*base78 + (2987185352221199943/1709500000000000000000000000000000 : ℝ)*base79 + (13138878749393/17095000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (558869/78125000000000000000 : ℝ)*base89 + (558869/78125000000000000000 : ℝ)*base91 + (558869/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1225_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (943/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10867/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1225_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1225_s4_0 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1063612419/5000000000 : ℝ)*x 0 + (5398193253/10000000000 : ℝ)*x 1 + (5260691457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063612419/5000000000 : ℝ)^4209 ≤ (12933040968117/100000000000000 : ℝ)^3185 := by
    have hnat : (1063612419 : ℕ)^4209*100000000000000^3185 ≤ 12933040968117^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063612419 5000000000 12933040968117 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398193253/10000000000 : ℝ)^4209 ≤ (8855118999761/20000000000000 : ℝ)^3185 := by
    have hnat : (5398193253 : ℕ)^4209*20000000000000^3185 ≤ 8855118999761^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398193253 10000000000 8855118999761 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260691457/10000000000 : ℝ)^4209 ≤ (42791364026219/100000000000000 : ℝ)^3185 := by
    have hnat : (5260691457 : ℕ)^4209*100000000000000^3185 ≤ 42791364026219^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260691457 10000000000 42791364026219 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1063612419/5000000000 : ℝ), (5398193253/10000000000 : ℝ), (5260691457/10000000000 : ℝ)] ![(12933040968117/100000000000000 : ℝ), (8855118999761/20000000000000 : ℝ), (42791364026219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1063612419/5000000000 : ℝ)|^4209 ≤ (12933040968117/100000000000000 : ℝ)^3185
        have hw : |(-1063612419/5000000000 : ℝ)|=(1063612419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398193253/10000000000 : ℝ)|^4209 ≤ (8855118999761/20000000000000 : ℝ)^3185
        have hw : |(5398193253/10000000000 : ℝ)|=(5398193253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260691457/10000000000 : ℝ)|^4209 ≤ (42791364026219/100000000000000 : ℝ)^3185
        have hw : |(5260691457/10000000000 : ℝ)|=(5260691457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s4_1 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673042551/5000000000 : ℝ)*x 0 + (-549261637/2500000000 : ℝ)*x 1 + (5260691359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673042551/5000000000 : ℝ)^4209 ≤ (341497484063/781250000000 : ℝ)^3185 := by
    have hnat : (2673042551 : ℕ)^4209*781250000000^3185 ≤ 341497484063^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673042551 5000000000 341497484063 781250000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549261637/2500000000 : ℝ)^4209 ≤ (674847952597/5000000000000 : ℝ)^3185 := by
    have hnat : (549261637 : ℕ)^4209*5000000000000^3185 ≤ 674847952597^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549261637 2500000000 674847952597 5000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260691359/10000000000 : ℝ)^4209 ≤ (21395681486391/50000000000000 : ℝ)^3185 := by
    have hnat : (5260691359 : ℕ)^4209*50000000000000^3185 ≤ 21395681486391^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260691359 10000000000 21395681486391 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673042551/5000000000 : ℝ), (-549261637/2500000000 : ℝ), (5260691359/10000000000 : ℝ)] ![(341497484063/781250000000 : ℝ), (674847952597/5000000000000 : ℝ), (21395681486391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673042551/5000000000 : ℝ)|^4209 ≤ (341497484063/781250000000 : ℝ)^3185
        have hw : |(2673042551/5000000000 : ℝ)|=(2673042551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-549261637/2500000000 : ℝ)|^4209 ≤ (674847952597/5000000000000 : ℝ)^3185
        have hw : |(-549261637/2500000000 : ℝ)|=(549261637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260691359/10000000000 : ℝ)|^4209 ≤ (21395681486391/50000000000000 : ℝ)^3185
        have hw : |(5260691359/10000000000 : ℝ)|=(5260691359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s4_2 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41766287/78125000 : ℝ)*x 0 + (2630345703/5000000000 : ℝ)*x 1 + (-549261743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41766287/78125000 : ℝ)^4209 ≤ (43711674005377/100000000000000 : ℝ)^3185 := by
    have hnat : (41766287 : ℕ)^4209*100000000000000^3185 ≤ 43711674005377^3185*78125000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41766287 78125000 43711674005377 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630345703/5000000000 : ℝ)^4209 ≤ (21395681739001/50000000000000 : ℝ)^3185 := by
    have hnat : (2630345703 : ℕ)^4209*50000000000000^3185 ≤ 21395681739001^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630345703 5000000000 21395681739001 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549261743/2500000000 : ℝ)^4209 ≤ (3374240623527/25000000000000 : ℝ)^3185 := by
    have hnat : (549261743 : ℕ)^4209*25000000000000^3185 ≤ 3374240623527^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549261743 2500000000 3374240623527 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41766287/78125000 : ℝ), (2630345703/5000000000 : ℝ), (-549261743/2500000000 : ℝ)] ![(43711674005377/100000000000000 : ℝ), (21395681739001/50000000000000 : ℝ), (3374240623527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41766287/78125000 : ℝ)|^4209 ≤ (43711674005377/100000000000000 : ℝ)^3185
        have hw : |(41766287/78125000 : ℝ)|=(41766287/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630345703/5000000000 : ℝ)|^4209 ≤ (21395681739001/50000000000000 : ℝ)^3185
        have hw : |(2630345703/5000000000 : ℝ)|=(2630345703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-549261743/2500000000 : ℝ)|^4209 ≤ (3374240623527/25000000000000 : ℝ)^3185
        have hw : |(-549261743/2500000000 : ℝ)|=(549261743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s4_3 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4352764679/10000000000 : ℝ)*x 0 + (843184581/2000000000 : ℝ)*x 1 + (1123484891/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352764679/10000000000 : ℝ)^4209 ≤ (6662782566907/20000000000000 : ℝ)^3185 := by
    have hnat : (4352764679 : ℕ)^4209*20000000000000^3185 ≤ 6662782566907^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352764679 10000000000 6662782566907 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (843184581/2000000000 : ℝ)^4209 ≤ (798422945833/2500000000000 : ℝ)^3185 := by
    have hnat : (843184581 : ℕ)^4209*2500000000000^3185 ≤ 798422945833^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843184581 2000000000 798422945833 2500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123484891/2500000000 : ℝ)^4209 ≤ (34749169324739/100000000000000 : ℝ)^3185 := by
    have hnat : (1123484891 : ℕ)^4209*100000000000000^3185 ≤ 34749169324739^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123484891 2500000000 34749169324739 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352764679/10000000000 : ℝ), (843184581/2000000000 : ℝ), (1123484891/2500000000 : ℝ)] ![(6662782566907/20000000000000 : ℝ), (798422945833/2500000000000 : ℝ), (34749169324739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352764679/10000000000 : ℝ)|^4209 ≤ (6662782566907/20000000000000 : ℝ)^3185
        have hw : |(4352764679/10000000000 : ℝ)|=(4352764679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(843184581/2000000000 : ℝ)|^4209 ≤ (798422945833/2500000000000 : ℝ)^3185
        have hw : |(843184581/2000000000 : ℝ)|=(843184581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123484891/2500000000 : ℝ)|^4209 ≤ (34749169324739/100000000000000 : ℝ)^3185
        have hw : |(1123484891/2500000000 : ℝ)|=(1123484891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s4_4 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-106361533/500000000 : ℝ)*x 0 + (2630537027/5000000000 : ℝ)*x 1 + (1349452373/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106361533/500000000 : ℝ)^4209 ≤ (12933087744769/100000000000000 : ℝ)^3185 := by
    have hnat : (106361533 : ℕ)^4209*100000000000000^3185 ≤ 12933087744769^3185*500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106361533 500000000 12933087744769 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630537027/5000000000 : ℝ)^4209 ≤ (427954767489/1000000000000 : ℝ)^3185 := by
    have hnat : (2630537027 : ℕ)^4209*1000000000000^3185 ≤ 427954767489^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630537027 5000000000 427954767489 1000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349452373/2500000000 : ℝ)^4209 ≤ (44271435496771/100000000000000 : ℝ)^3185 := by
    have hnat : (1349452373 : ℕ)^4209*100000000000000^3185 ≤ 44271435496771^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349452373 2500000000 44271435496771 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106361533/500000000 : ℝ), (2630537027/5000000000 : ℝ), (1349452373/2500000000 : ℝ)] ![(12933087744769/100000000000000 : ℝ), (427954767489/1000000000000 : ℝ), (44271435496771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106361533/500000000 : ℝ)|^4209 ≤ (12933087744769/100000000000000 : ℝ)^3185
        have hw : |(-106361533/500000000 : ℝ)|=(106361533/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630537027/5000000000 : ℝ)|^4209 ≤ (427954767489/1000000000000 : ℝ)^3185
        have hw : |(2630537027/5000000000 : ℝ)|=(2630537027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349452373/2500000000 : ℝ)|^4209 ≤ (44271435496771/100000000000000 : ℝ)^3185
        have hw : |(1349452373/2500000000 : ℝ)|=(1349452373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s4_5 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311043207/10000000000 : ℝ)*x 0 + (-411985789/2000000000 : ℝ)*x 1 + (2698904553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311043207/10000000000 : ℝ)^4209 ≤ (43333444322071/100000000000000 : ℝ)^3185 := by
    have hnat : (5311043207 : ℕ)^4209*100000000000000^3185 ≤ 43333444322071^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311043207 10000000000 43333444322071 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411985789/2000000000 : ℝ)^4209 ≤ (12395124352009/100000000000000 : ℝ)^3185 := by
    have hnat : (411985789 : ℕ)^4209*100000000000000^3185 ≤ 12395124352009^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411985789 2000000000 12395124352009 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698904553/5000000000 : ℝ)^4209 ≤ (5533928914131/12500000000000 : ℝ)^3185 := by
    have hnat : (2698904553 : ℕ)^4209*12500000000000^3185 ≤ 5533928914131^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698904553 5000000000 5533928914131 12500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311043207/10000000000 : ℝ), (-411985789/2000000000 : ℝ), (2698904553/5000000000 : ℝ)] ![(43333444322071/100000000000000 : ℝ), (12395124352009/100000000000000 : ℝ), (5533928914131/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311043207/10000000000 : ℝ)|^4209 ≤ (43333444322071/100000000000000 : ℝ)^3185
        have hw : |(5311043207/10000000000 : ℝ)|=(5311043207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-411985789/2000000000 : ℝ)|^4209 ≤ (12395124352009/100000000000000 : ℝ)^3185
        have hw : |(-411985789/2000000000 : ℝ)|=(411985789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698904553/5000000000 : ℝ)|^4209 ≤ (5533928914131/12500000000000 : ℝ)^3185
        have hw : |(2698904553/5000000000 : ℝ)|=(2698904553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s4_6 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311042941/10000000000 : ℝ)*x 0 + (5397809479/10000000000 : ℝ)*x 1 + (-1029964399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311042941/10000000000 : ℝ)^4209 ≤ (43333441453969/100000000000000 : ℝ)^3185 := by
    have hnat : (5311042941 : ℕ)^4209*100000000000000^3185 ≤ 43333441453969^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311042941 10000000000 43333441453969 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397809479/10000000000 : ℝ)^4209 ≤ (11067858838967/25000000000000 : ℝ)^3185 := by
    have hnat : (5397809479 : ℕ)^4209*25000000000000^3185 ≤ 11067858838967^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397809479 10000000000 11067858838967 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029964399/5000000000 : ℝ)^4209 ≤ (12395123183087/100000000000000 : ℝ)^3185 := by
    have hnat : (1029964399 : ℕ)^4209*100000000000000^3185 ≤ 12395123183087^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029964399 5000000000 12395123183087 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311042941/10000000000 : ℝ), (5397809479/10000000000 : ℝ), (-1029964399/5000000000 : ℝ)] ![(43333441453969/100000000000000 : ℝ), (11067858838967/25000000000000 : ℝ), (12395123183087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311042941/10000000000 : ℝ)|^4209 ≤ (43333441453969/100000000000000 : ℝ)^3185
        have hw : |(5311042941/10000000000 : ℝ)|=(5311042941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397809479/10000000000 : ℝ)|^4209 ≤ (11067858838967/25000000000000 : ℝ)^3185
        have hw : |(5397809479/10000000000 : ℝ)|=(5397809479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1029964399/5000000000 : ℝ)|^4209 ≤ (12395123183087/100000000000000 : ℝ)^3185
        have hw : |(-1029964399/5000000000 : ℝ)|=(1029964399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s4_7 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1088194519/2500000000 : ℝ)*x 0 + (179726647/400000000 : ℝ)*x 1 + (4216698757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088194519/2500000000 : ℝ)^4209 ≤ (33314048334043/100000000000000 : ℝ)^3185 := by
    have hnat : (1088194519 : ℕ)^4209*100000000000000^3185 ≤ 33314048334043^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088194519 2500000000 33314048334043 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179726647/400000000 : ℝ)^4209 ≤ (34741266676263/100000000000000 : ℝ)^3185 := by
    have hnat : (179726647 : ℕ)^4209*100000000000000^3185 ≤ 34741266676263^3185*400000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179726647 400000000 34741266676263 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4216698757/10000000000 : ℝ)^4209 ≤ (6388936996193/20000000000000 : ℝ)^3185 := by
    have hnat : (4216698757 : ℕ)^4209*20000000000000^3185 ≤ 6388936996193^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216698757 10000000000 6388936996193 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088194519/2500000000 : ℝ), (179726647/400000000 : ℝ), (4216698757/10000000000 : ℝ)] ![(33314048334043/100000000000000 : ℝ), (34741266676263/100000000000000 : ℝ), (6388936996193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088194519/2500000000 : ℝ)|^4209 ≤ (33314048334043/100000000000000 : ℝ)^3185
        have hw : |(1088194519/2500000000 : ℝ)|=(1088194519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179726647/400000000 : ℝ)|^4209 ≤ (34741266676263/100000000000000 : ℝ)^3185
        have hw : |(179726647/400000000 : ℝ)|=(179726647/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4216698757/10000000000 : ℝ)|^4209 ≤ (6388936996193/20000000000000 : ℝ)^3185
        have hw : |(4216698757/10000000000 : ℝ)|=(4216698757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1225_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10867/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2831/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14717/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10867/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14717/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10867/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14717/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10867/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14717/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10867/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14717/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10867/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14717/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10867/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10867/100000 : ℝ) ^ (8417/2048 : ℝ) ≤ (10928045976359127/100000000000000000000 : ℝ) := by
    have hpowers : (10867/100000 : ℝ)^8417 ≤ (10928045976359127/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10867 : ℕ)^8417*100000000000000000000^2048 ≤ 10928045976359127^2048*100000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10867 100000 10928045976359127 100000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10867/100000 : ℝ)) (X := (10928045976359127/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14717/100000 : ℝ) ^ (8417/2048 : ℝ) ≤ (38005903044194763/100000000000000000000 : ℝ) := by
    have hpowers : (14717/100000 : ℝ)^8417 ≤ (38005903044194763/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14717 : ℕ)^8417*100000000000000000000^2048 ≤ 38005903044194763^2048*100000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14717 100000 38005903044194763 100000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14717/100000 : ℝ)) (X := (38005903044194763/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010928045976359127/50000000000000000000 : ℝ) ≤ (1250066469014277/1250000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (50010928045976359127/50000000000000000000 : ℝ)^2048 ≤ (1250066469014277/1250000000000000 : ℝ)^8417 := by
      have hnat : (50010928045976359127 : ℕ)^2048*1250000000000000^8417 ≤ 1250066469014277^8417*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010928045976359127 50000000000000000000 1250066469014277 1250000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250066469014277/1250000000000000 : ℝ)) (X := (50010928045976359127/50000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004893394902055389/10000000000000000000 : ℝ) ≤ (5000595213134389/5000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (10004893394902055389/10000000000000000000 : ℝ)^2048 ≤ (5000595213134389/5000000000000000 : ℝ)^8417 := by
      have hnat : (10004893394902055389 : ℕ)^2048*5000000000000000^8417 ≤ 5000595213134389^8417*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004893394902055389 10000000000000000000 5000595213134389 5000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000595213134389/5000000000000000 : ℝ)) (X := (10004893394902055389/10000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038005903044194763/50000000000000000000 : ℝ) ≤ (500092455021167/500000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (50038005903044194763/50000000000000000000 : ℝ)^2048 ≤ (500092455021167/500000000000000 : ℝ)^8417 := by
      have hnat : (50038005903044194763 : ℕ)^2048*500000000000000^8417 ≤ 500092455021167^8417*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038005903044194763 50000000000000000000 500092455021167 500000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500092455021167/500000000000000 : ℝ)) (X := (50038005903044194763/50000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10928045976359127/100000000000000000000 : ℝ) ≤ ((9621932905391120273/9625000000000000000 : ℝ)+2*(329337077281/192500000000000 : ℝ)*(10867/100000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (9621932905391120273/9625000000000000000 : ℝ)+2*(329337077281/192500000000000 : ℝ)*(10867/100000 : ℝ)=(1250066469014277/1250000000000000 : ℝ) by norm_num, show 1+2*(10928045976359127/100000000000000000000 : ℝ)=(50010928045976359127/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38005903044194763/100000000000000000000 : ℝ)+(10928045976359127/100000000000000000000 : ℝ) ≤ ((9621932905391120273/9625000000000000000 : ℝ)+(329337077281/192500000000000 : ℝ)*((14717/100000 : ℝ)+(10867/100000 : ℝ)))^(8417/2048 : ℝ) := by
    rw [show (9621932905391120273/9625000000000000000 : ℝ)+(329337077281/192500000000000 : ℝ)*((14717/100000 : ℝ)+(10867/100000 : ℝ))=(5000595213134389/5000000000000000 : ℝ) by norm_num, show 1+(38005903044194763/100000000000000000000 : ℝ)+(10928045976359127/100000000000000000000 : ℝ)=(10004893394902055389/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38005903044194763/100000000000000000000 : ℝ) ≤ ((9621932905391120273/9625000000000000000 : ℝ)+2*(329337077281/192500000000000 : ℝ)*(14717/100000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (9621932905391120273/9625000000000000000 : ℝ)+2*(329337077281/192500000000000 : ℝ)*(14717/100000 : ℝ)=(500092455021167/500000000000000 : ℝ) by norm_num, show 1+2*(38005903044194763/100000000000000000000 : ℝ)=(50038005903044194763/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9621932905391120273/9625000000000000000 : ℝ)*(X 1 0+X 2 0)+(329337077281/192500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (10867/100000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (9621932905391120273/9625000000000000000 : ℝ)) (alpha := (329337077281/192500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9621932905391120273/9625000000000000000 : ℝ)*(X 0 1+X 2 1)+(329337077281/192500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (10867/100000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (9621932905391120273/9625000000000000000 : ℝ)) (alpha := (329337077281/192500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9621932905391120273/9625000000000000000 : ℝ)*(X 0 2+X 1 2)+(329337077281/192500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (10867/100000 : ℝ)) (hi := (14717/100000 : ℝ)) (c := (9621932905391120273/9625000000000000000 : ℝ)) (alpha := (329337077281/192500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1063612419/5000000000 : ℝ)*X 0 0+(5398193253/10000000000 : ℝ)*X 0 1+(5260691457/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673042551/5000000000 : ℝ)*X 1 0+(-549261637/2500000000 : ℝ)*X 1 1+(5260691359/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((41766287/78125000 : ℝ)*X 2 0+(2630345703/5000000000 : ℝ)*X 2 1+(-549261743/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352764679/10000000000 : ℝ)*X 0 0+(843184581/2000000000 : ℝ)*X 0 1+(1123484891/2500000000 : ℝ)*X 0 2+(4352764679/10000000000 : ℝ)*X 1 0+(843184581/2000000000 : ℝ)*X 1 1+(1123484891/2500000000 : ℝ)*X 1 2+(4352764679/10000000000 : ℝ)*X 2 0+(843184581/2000000000 : ℝ)*X 2 1+(1123484891/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-106361533/500000000 : ℝ)*X 0 0+(2630537027/5000000000 : ℝ)*X 0 1+(1349452373/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311043207/10000000000 : ℝ)*X 1 0+(-411985789/2000000000 : ℝ)*X 1 1+(2698904553/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311042941/10000000000 : ℝ)*X 2 0+(5397809479/10000000000 : ℝ)*X 2 1+(-1029964399/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1088194519/2500000000 : ℝ)*X 0 0+(179726647/400000000 : ℝ)*X 0 1+(4216698757/10000000000 : ℝ)*X 0 2+(1088194519/2500000000 : ℝ)*X 1 0+(179726647/400000000 : ℝ)*X 1 1+(4216698757/10000000000 : ℝ)*X 1 2+(1088194519/2500000000 : ℝ)*X 2 0+(179726647/400000000 : ℝ)*X 2 1+(4216698757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33359128247403079235392317/43750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41174063/5000000000000 : ℝ)*(base19) + (101568317/12500000000000 : ℝ)*(base23) + (29375051/10000000000000 : ℝ)*(upper2) + (74437817/100000000000000 : ℝ)*(upper3) + (5434808038143209/100000000000000 : ℝ)*(major0) + (5434808038143209/100000000000000 : ℝ)*(major1) + (5434808038143209/100000000000000 : ℝ)*(major2) + (7272667047521247/100000000000000 : ℝ)*(sp0) + (1818171014997747/25000000000000 : ℝ)*(sp1) + (227271079214519/3125000000000 : ℝ)*(sp2) + (719384166651497/20000000000000 : ℝ)*(sp3) + (17835951/100000000000 : ℝ)*(sp4) + (596003819/6250000000000 : ℝ)*(sp6) + (10334140199/100000000000000 : ℝ)*(sp7) + (899232791849421/25000000000000 : ℝ)*(f.failure) + (7272684883472247/100000000000000 : ℝ)*(f.sum) + (846045681241/218750000000000000000000000 : ℝ)*base65 + (1262696373508284187/87500000000000000000000000000000 : ℝ)*base67 + (1423198951670784187/87500000000000000000000000000000 : ℝ)*base69 + (325471013283284187/87500000000000000000000000000000 : ℝ)*base71 + (3206385461089/875000000000000000000000000 : ℝ)*base73 + (161125743033284187/87500000000000000000000000000000 : ℝ)*base75 + (605625925383284187/87500000000000000000000000000000 : ℝ)*base77 + (411438345870784187/87500000000000000000000000000000 : ℝ)*base79 + (3334915779107/437500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (198583/625000000000000000000 : ℝ)*base89 + (198583/625000000000000000000 : ℝ)*base91 + (198583/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8803826913928555088950113/1093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (146076483/10000000000000 : ℝ)*(base19) + (1898385403/100000000000000 : ℝ)*(base23) + (7900581/6250000000000 : ℝ)*(upper3) + (68832711/20000000000000 : ℝ)*(lower4) + (110570847/100000000000000 : ℝ)*(upper5) + (136630498953953/2500000000000 : ℝ)*(major0) + (136630498953953/2500000000000 : ℝ)*(major1) + (136630498953953/2500000000000 : ℝ)*(major2) + (19221878019/100000000000000 : ℝ)*(sp1) + (4284929091/10000000000000 : ℝ)*(sp2) + (3656690445761891/50000000000000 : ℝ)*(sp4) + (3656680104440467/50000000000000 : ℝ)*(sp5) + (7313336143847469/100000000000000 : ℝ)*(sp6) + (180852937824267/5000000000000 : ℝ)*(sp7) + (180852937824267/5000000000000 : ℝ)*(f.failure) + (3656690445761891/50000000000000 : ℝ)*(f.sum) + (127075676459/120312500000000000000000000 : ℝ)*base65 + (321443921508939169/24062500000000000000000000000000 : ℝ)*base67 + (15216500105189169/24062500000000000000000000000000 : ℝ)*base69 + (380522956235189169/24062500000000000000000000000000 : ℝ)*base71 + (6534365988847/962500000000000000000000000 : ℝ)*base73 + (299929679343873331/24062500000000000000000000000000 : ℝ)*base76 + (434470411984876669/24062500000000000000000000000000 : ℝ)*base77 + (186879420050748331/24062500000000000000000000000000 : ℝ)*base80 + (2076615370903/962500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (810559/125000000000000000000 : ℝ)*base90 + (810559/125000000000000000000 : ℝ)*base92 + (810559/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1225_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10867/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1225_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1225_s5_0 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2127700837/10000000000 : ℝ)*x 0 + (2696410467/5000000000 : ℝ)*x 1 + (5265751087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127700837/10000000000 : ℝ)^4209 ≤ (323421637527/2500000000000 : ℝ)^3185 := by
    have hnat : (2127700837 : ℕ)^4209*2500000000000^3185 ≤ 323421637527^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127700837 10000000000 323421637527 2500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696410467/5000000000 : ℝ)^4209 ≤ (22108687126881/50000000000000 : ℝ)^3185 := by
    have hnat : (2696410467 : ℕ)^4209*50000000000000^3185 ≤ 22108687126881^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696410467 5000000000 22108687126881 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265751087/10000000000 : ℝ)^4209 ≤ (535572003003/1250000000000 : ℝ)^3185 := by
    have hnat : (5265751087 : ℕ)^4209*1250000000000^3185 ≤ 535572003003^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265751087 10000000000 535572003003 1250000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2127700837/10000000000 : ℝ), (2696410467/5000000000 : ℝ), (5265751087/10000000000 : ℝ)] ![(323421637527/2500000000000 : ℝ), (22108687126881/50000000000000 : ℝ), (535572003003/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2127700837/10000000000 : ℝ)|^4209 ≤ (323421637527/2500000000000 : ℝ)^3185
        have hw : |(-2127700837/10000000000 : ℝ)|=(2127700837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696410467/5000000000 : ℝ)|^4209 ≤ (22108687126881/50000000000000 : ℝ)^3185
        have hw : |(2696410467/5000000000 : ℝ)|=(2696410467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265751087/10000000000 : ℝ)|^4209 ≤ (535572003003/1250000000000 : ℝ)^3185
        have hw : |(5265751087/10000000000 : ℝ)|=(5265751087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s5_1 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336181937/2500000000 : ℝ)*x 0 + (-2192150731/10000000000 : ℝ)*x 1 + (2632875549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336181937/2500000000 : ℝ)^4209 ≤ (43697012135033/100000000000000 : ℝ)^3185 := by
    have hnat : (1336181937 : ℕ)^4209*100000000000000^3185 ≤ 43697012135033^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336181937 2500000000 43697012135033 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2192150731/10000000000 : ℝ)^4209 ≤ (6728613744063/50000000000000 : ℝ)^3185 := by
    have hnat : (2192150731 : ℕ)^4209*50000000000000^3185 ≤ 6728613744063^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192150731 10000000000 6728613744063 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632875549/5000000000 : ℝ)^4209 ≤ (42845760358519/100000000000000 : ℝ)^3185 := by
    have hnat : (2632875549 : ℕ)^4209*100000000000000^3185 ≤ 42845760358519^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632875549 5000000000 42845760358519 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336181937/2500000000 : ℝ), (-2192150731/10000000000 : ℝ), (2632875549/5000000000 : ℝ)] ![(43697012135033/100000000000000 : ℝ), (6728613744063/50000000000000 : ℝ), (42845760358519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336181937/2500000000 : ℝ)|^4209 ≤ (43697012135033/100000000000000 : ℝ)^3185
        have hw : |(1336181937/2500000000 : ℝ)|=(1336181937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2192150731/10000000000 : ℝ)|^4209 ≤ (6728613744063/50000000000000 : ℝ)^3185
        have hw : |(-2192150731/10000000000 : ℝ)|=(2192150731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632875549/5000000000 : ℝ)|^4209 ≤ (42845760358519/100000000000000 : ℝ)^3185
        have hw : |(2632875549/5000000000 : ℝ)|=(2632875549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s5_2 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334045487/625000000 : ℝ)*x 0 + (5265751153/10000000000 : ℝ)*x 1 + (-10960753/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334045487/625000000 : ℝ)^4209 ≤ (43697012610421/100000000000000 : ℝ)^3185 := by
    have hnat : (334045487 : ℕ)^4209*100000000000000^3185 ≤ 43697012610421^3185*625000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334045487 625000000 43697012610421 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265751153/10000000000 : ℝ)^4209 ≤ (42845760949917/100000000000000 : ℝ)^3185 := by
    have hnat : (5265751153 : ℕ)^4209*100000000000000^3185 ≤ 42845760949917^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265751153 10000000000 42845760949917 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10960753/50000000 : ℝ)^4209 ≤ (13457226425389/100000000000000 : ℝ)^3185 := by
    have hnat : (10960753 : ℕ)^4209*100000000000000^3185 ≤ 13457226425389^3185*50000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10960753 50000000 13457226425389 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334045487/625000000 : ℝ), (5265751153/10000000000 : ℝ), (-10960753/50000000 : ℝ)] ![(43697012610421/100000000000000 : ℝ), (42845760949917/100000000000000 : ℝ), (13457226425389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334045487/625000000 : ℝ)|^4209 ≤ (43697012610421/100000000000000 : ℝ)^3185
        have hw : |(334045487/625000000 : ℝ)|=(334045487/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265751153/10000000000 : ℝ)|^4209 ≤ (42845760949917/100000000000000 : ℝ)^3185
        have hw : |(5265751153/10000000000 : ℝ)|=(5265751153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10960753/50000000 : ℝ)|^4209 ≤ (13457226425389/100000000000000 : ℝ)^3185
        have hw : |(-10960753/50000000 : ℝ)|=(10960753/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s5_3 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4353045011/10000000000 : ℝ)*x 0 + (1056608341/2500000000 : ℝ)*x 1 + (4483357097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353045011/10000000000 : ℝ)^4209 ≤ (33316748187411/100000000000000 : ℝ)^3185 := by
    have hnat : (4353045011 : ℕ)^4209*100000000000000^3185 ≤ 33316748187411^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353045011 10000000000 33316748187411 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056608341/2500000000 : ℝ)^4209 ≤ (16021089166707/50000000000000 : ℝ)^3185 := by
    have hnat : (1056608341 : ℕ)^4209*50000000000000^3185 ≤ 16021089166707^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056608341 2500000000 16021089166707 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483357097/10000000000 : ℝ)^4209 ≤ (34641073457091/100000000000000 : ℝ)^3185 := by
    have hnat : (4483357097 : ℕ)^4209*100000000000000^3185 ≤ 34641073457091^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483357097 10000000000 34641073457091 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353045011/10000000000 : ℝ), (1056608341/2500000000 : ℝ), (4483357097/10000000000 : ℝ)] ![(33316748187411/100000000000000 : ℝ), (16021089166707/50000000000000 : ℝ), (34641073457091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353045011/10000000000 : ℝ)|^4209 ≤ (33316748187411/100000000000000 : ℝ)^3185
        have hw : |(4353045011/10000000000 : ℝ)|=(4353045011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056608341/2500000000 : ℝ)|^4209 ≤ (16021089166707/50000000000000 : ℝ)^3185
        have hw : |(1056608341/2500000000 : ℝ)|=(1056608341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483357097/10000000000 : ℝ)|^4209 ≤ (34641073457091/100000000000000 : ℝ)^3185
        have hw : |(4483357097/10000000000 : ℝ)|=(4483357097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s5_4 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2127705651/10000000000 : ℝ)*x 0 + (526607799/1000000000 : ℝ)*x 1 + (107849859/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127705651/10000000000 : ℝ)^4209 ≤ (12936904181771/100000000000000 : ℝ)^3185 := by
    have hnat : (2127705651 : ℕ)^4209*100000000000000^3185 ≤ 12936904181771^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127705651 10000000000 12936904181771 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526607799/1000000000 : ℝ)^4209 ≤ (8569855072211/20000000000000 : ℝ)^3185 := by
    have hnat : (526607799 : ℕ)^4209*20000000000000^3185 ≤ 8569855072211^3185*1000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526607799 1000000000 8569855072211 20000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107849859/200000000 : ℝ)^4209 ≤ (552672755481/1250000000000 : ℝ)^3185 := by
    have hnat : (107849859 : ℕ)^4209*1250000000000^3185 ≤ 552672755481^3185*200000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107849859 200000000 552672755481 1250000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2127705651/10000000000 : ℝ), (526607799/1000000000 : ℝ), (107849859/200000000 : ℝ)] ![(12936904181771/100000000000000 : ℝ), (8569855072211/20000000000000 : ℝ), (552672755481/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2127705651/10000000000 : ℝ)|^4209 ≤ (12936904181771/100000000000000 : ℝ)^3185
        have hw : |(-2127705651/10000000000 : ℝ)|=(2127705651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526607799/1000000000 : ℝ)|^4209 ≤ (8569855072211/20000000000000 : ℝ)^3185
        have hw : |(526607799/1000000000 : ℝ)|=(526607799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107849859/200000000 : ℝ)|^4209 ≤ (552672755481/1250000000000 : ℝ)^3185
        have hw : |(107849859/200000000 : ℝ)|=(107849859/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s5_5 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062468599/2000000000 : ℝ)*x 0 + (-206540897/1000000000 : ℝ)*x 1 + (5392493007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062468599/2000000000 : ℝ)^4209 ≤ (21673729812227/50000000000000 : ℝ)^3185 := by
    have hnat : (1062468599 : ℕ)^4209*50000000000000^3185 ≤ 21673729812227^3185*2000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062468599 2000000000 21673729812227 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206540897/1000000000 : ℝ)^4209 ≤ (1554839913613/12500000000000 : ℝ)^3185 := by
    have hnat : (206540897 : ℕ)^4209*12500000000000^3185 ≤ 1554839913613^3185*1000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206540897 1000000000 1554839913613 12500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392493007/10000000000 : ℝ)^4209 ≤ (5526727632011/12500000000000 : ℝ)^3185 := by
    have hnat : (5392493007 : ℕ)^4209*12500000000000^3185 ≤ 5526727632011^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392493007 10000000000 5526727632011 12500000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062468599/2000000000 : ℝ), (-206540897/1000000000 : ℝ), (5392493007/10000000000 : ℝ)] ![(21673729812227/50000000000000 : ℝ), (1554839913613/12500000000000 : ℝ), (5526727632011/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062468599/2000000000 : ℝ)|^4209 ≤ (21673729812227/50000000000000 : ℝ)^3185
        have hw : |(1062468599/2000000000 : ℝ)|=(1062468599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-206540897/1000000000 : ℝ)|^4209 ≤ (1554839913613/12500000000000 : ℝ)^3185
        have hw : |(-206540897/1000000000 : ℝ)|=(206540897/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392493007/10000000000 : ℝ)|^4209 ≤ (5526727632011/12500000000000 : ℝ)^3185
        have hw : |(5392493007/10000000000 : ℝ)|=(5392493007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s5_6 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328085813/2500000000 : ℝ)*x 0 + (43139943/80000000 : ℝ)*x 1 + (-2065408801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328085813/2500000000 : ℝ)^4209 ≤ (10836865598933/25000000000000 : ℝ)^3185 := by
    have hnat : (1328085813 : ℕ)^4209*25000000000000^3185 ≤ 10836865598933^3185*2500000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328085813 2500000000 10836865598933 25000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43139943/80000000 : ℝ)^4209 ≤ (22106909812919/50000000000000 : ℝ)^3185 := by
    have hnat : (43139943 : ℕ)^4209*50000000000000^3185 ≤ 22106909812919^3185*80000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43139943 80000000 22106909812919 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065408801/10000000000 : ℝ)^4209 ≤ (12438717963893/100000000000000 : ℝ)^3185 := by
    have hnat : (2065408801 : ℕ)^4209*100000000000000^3185 ≤ 12438717963893^3185*10000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065408801 10000000000 12438717963893 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328085813/2500000000 : ℝ), (43139943/80000000 : ℝ), (-2065408801/10000000000 : ℝ)] ![(10836865598933/25000000000000 : ℝ), (22106909812919/50000000000000 : ℝ), (12438717963893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328085813/2500000000 : ℝ)|^4209 ≤ (10836865598933/25000000000000 : ℝ)^3185
        have hw : |(1328085813/2500000000 : ℝ)|=(1328085813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43139943/80000000 : ℝ)|^4209 ≤ (22106909812919/50000000000000 : ℝ)^3185
        have hw : |(43139943/80000000 : ℝ)|=(43139943/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2065408801/10000000000 : ℝ)|^4209 ≤ (12438717963893/100000000000000 : ℝ)^3185
        have hw : |(-2065408801/10000000000 : ℝ)|=(2065408801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1225_s5_7 (p : ℝ) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2176527519/5000000000 : ℝ)*x 0 + (560337077/1250000000 : ℝ)*x 1 + (2113548171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176527519/5000000000 : ℝ)^4209 ≤ (1665842480213/5000000000000 : ℝ)^3185 := by
    have hnat : (2176527519 : ℕ)^4209*5000000000000^3185 ≤ 1665842480213^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176527519 5000000000 1665842480213 5000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560337077/1250000000 : ℝ)^4209 ≤ (17317164806337/50000000000000 : ℝ)^3185 := by
    have hnat : (560337077 : ℕ)^4209*50000000000000^3185 ≤ 17317164806337^3185*1250000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560337077 1250000000 17317164806337 50000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113548171/5000000000 : ℝ)^4209 ≤ (32048820772253/100000000000000 : ℝ)^3185 := by
    have hnat : (2113548171 : ℕ)^4209*100000000000000^3185 ≤ 32048820772253^3185*5000000000^4209 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113548171 5000000000 32048820772253 100000000000000 4209 3185 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4209/1024 : ℝ)) 4209 3185 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176527519/5000000000 : ℝ), (560337077/1250000000 : ℝ), (2113548171/5000000000 : ℝ)] ![(1665842480213/5000000000000 : ℝ), (17317164806337/50000000000000 : ℝ), (32048820772253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176527519/5000000000 : ℝ)|^4209 ≤ (1665842480213/5000000000000 : ℝ)^3185
        have hw : |(2176527519/5000000000 : ℝ)|=(2176527519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560337077/1250000000 : ℝ)|^4209 ≤ (17317164806337/50000000000000 : ℝ)^3185
        have hw : |(560337077/1250000000 : ℝ)|=(560337077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113548171/5000000000 : ℝ)|^4209 ≤ (32048820772253/100000000000000 : ℝ)^3185
        have hw : |(2113548171/5000000000 : ℝ)|=(2113548171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1225_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11431/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14123/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2831/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2831/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2831/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2831/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2831/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2831/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2831/25000 : ℝ) ^ (8417/2048 : ℝ) ≤ (12944007723488313/100000000000000000000 : ℝ) := by
    have hpowers : (2831/25000 : ℝ)^8417 ≤ (12944007723488313/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2831 : ℕ)^8417*100000000000000000000^2048 ≤ 12944007723488313^2048*25000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2831 25000 12944007723488313 100000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2831/25000 : ℝ)) (X := (12944007723488313/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (8417/2048 : ℝ) ≤ (16577168317144437/50000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^8417 ≤ (16577168317144437/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3559 : ℕ)^8417*50000000000000000000^2048 ≤ 16577168317144437^2048*25000^8417 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 16577168317144437 50000000000000000000 8417 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (16577168317144437/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012944007723488313/50000000000000000000 : ℝ) ≤ (5000314918994329/5000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (50012944007723488313/50000000000000000000 : ℝ)^2048 ≤ (5000314918994329/5000000000000000 : ℝ)^8417 := by
      have hnat : (50012944007723488313 : ℕ)^2048*5000000000000000^8417 ≤ 5000314918994329^8417*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012944007723488313 50000000000000000000 5000314918994329 5000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000314918994329/5000000000000000 : ℝ)) (X := (50012944007723488313/50000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046098344357777187/100000000000000000000 : ℝ) ≤ (2000224291191217/2000000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (100046098344357777187/100000000000000000000 : ℝ)^2048 ≤ (2000224291191217/2000000000000000 : ℝ)^8417 := by
      have hnat : (100046098344357777187 : ℕ)^2048*2000000000000000^8417 ≤ 2000224291191217^8417*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046098344357777187 100000000000000000000 2000224291191217 2000000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000224291191217/2000000000000000 : ℝ)) (X := (100046098344357777187/100000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016577168317144437/25000000000000000000 : ℝ) ≤ (1250201634240439/1250000000000000 : ℝ) ^ (8417/2048 : ℝ) := by
    have hpowers : (25016577168317144437/25000000000000000000 : ℝ)^2048 ≤ (1250201634240439/1250000000000000 : ℝ)^8417 := by
      have hnat : (25016577168317144437 : ℕ)^2048*1250000000000000^8417 ≤ 1250201634240439^8417*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016577168317144437 25000000000000000000 1250201634240439 1250000000000000 2048 8417 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250201634240439/1250000000000000 : ℝ)) (X := (25016577168317144437/25000000000000000000 : ℝ)) (by norm_num) 8417 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12944007723488313/100000000000000000000 : ℝ) ≤ ((145553499622483427/145600000000000000 : ℝ)+2*(491617967427/291200000000000 : ℝ)*(2831/25000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (145553499622483427/145600000000000000 : ℝ)+2*(491617967427/291200000000000 : ℝ)*(2831/25000 : ℝ)=(5000314918994329/5000000000000000 : ℝ) by norm_num, show 1+2*(12944007723488313/100000000000000000000 : ℝ)=(50012944007723488313/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16577168317144437/50000000000000000000 : ℝ)+(12944007723488313/100000000000000000000 : ℝ) ≤ ((145553499622483427/145600000000000000 : ℝ)+(491617967427/291200000000000 : ℝ)*((3559/25000 : ℝ)+(2831/25000 : ℝ)))^(8417/2048 : ℝ) := by
    rw [show (145553499622483427/145600000000000000 : ℝ)+(491617967427/291200000000000 : ℝ)*((3559/25000 : ℝ)+(2831/25000 : ℝ))=(2000224291191217/2000000000000000 : ℝ) by norm_num, show 1+(16577168317144437/50000000000000000000 : ℝ)+(12944007723488313/100000000000000000000 : ℝ)=(100046098344357777187/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16577168317144437/50000000000000000000 : ℝ) ≤ ((145553499622483427/145600000000000000 : ℝ)+2*(491617967427/291200000000000 : ℝ)*(3559/25000 : ℝ))^(8417/2048 : ℝ) := by
    rw [show (145553499622483427/145600000000000000 : ℝ)+2*(491617967427/291200000000000 : ℝ)*(3559/25000 : ℝ)=(1250201634240439/1250000000000000 : ℝ) by norm_num, show 1+2*(16577168317144437/50000000000000000000 : ℝ)=(25016577168317144437/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (145553499622483427/145600000000000000 : ℝ)*(X 1 0+X 2 0)+(491617967427/291200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (2831/25000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (145553499622483427/145600000000000000 : ℝ)) (alpha := (491617967427/291200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (145553499622483427/145600000000000000 : ℝ)*(X 0 1+X 2 1)+(491617967427/291200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (2831/25000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (145553499622483427/145600000000000000 : ℝ)) (alpha := (491617967427/291200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (145553499622483427/145600000000000000 : ℝ)*(X 0 2+X 1 2)+(491617967427/291200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8417/2048 : ℝ)) (lo := (2831/25000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (145553499622483427/145600000000000000 : ℝ)) (alpha := (491617967427/291200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2127700837/10000000000 : ℝ)*X 0 0+(2696410467/5000000000 : ℝ)*X 0 1+(5265751087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336181937/2500000000 : ℝ)*X 1 0+(-2192150731/10000000000 : ℝ)*X 1 1+(2632875549/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334045487/625000000 : ℝ)*X 2 0+(5265751153/10000000000 : ℝ)*X 2 1+(-10960753/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353045011/10000000000 : ℝ)*X 0 0+(1056608341/2500000000 : ℝ)*X 0 1+(4483357097/10000000000 : ℝ)*X 0 2+(4353045011/10000000000 : ℝ)*X 1 0+(1056608341/2500000000 : ℝ)*X 1 1+(4483357097/10000000000 : ℝ)*X 1 2+(4353045011/10000000000 : ℝ)*X 2 0+(1056608341/2500000000 : ℝ)*X 2 1+(4483357097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2127705651/10000000000 : ℝ)*X 0 0+(526607799/1000000000 : ℝ)*X 0 1+(107849859/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062468599/2000000000 : ℝ)*X 1 0+(-206540897/1000000000 : ℝ)*X 1 1+(5392493007/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328085813/2500000000 : ℝ)*X 2 0+(43139943/80000000 : ℝ)*X 2 1+(-2065408801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176527519/5000000000 : ℝ)*X 0 0+(560337077/1250000000 : ℝ)*X 0 1+(2113548171/5000000000 : ℝ)*X 0 2+(2176527519/5000000000 : ℝ)*X 1 0+(560337077/1250000000 : ℝ)*X 1 1+(2113548171/5000000000 : ℝ)*X 1 2+(2176527519/5000000000 : ℝ)*X 2 0+(560337077/1250000000 : ℝ)*X 2 1+(2113548171/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1225_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (222127888242467536862307/22750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (96538571/5000000000000 : ℝ)*(base19) + (1992886733/100000000000000 : ℝ)*(base23) + (714101/50000000000000 : ℝ)*(lower2) + (2077951/2500000000000 : ℝ)*(upper3) + (15207373/5000000000000 : ℝ)*(upper5) + (18378227285647/312500000000 : ℝ)*(major0) + (18378227285647/312500000000 : ℝ)*(major1) + (18378227285647/312500000000 : ℝ)*(major2) + (3934870918269239/50000000000000 : ℝ)*(sp0) + (7869806151755293/100000000000000 : ℝ)*(sp1) + (393490304481999/5000000000000 : ℝ)*(sp2) + (389223331127831/10000000000000 : ℝ)*(sp3) + (13249197647/20000000000000 : ℝ)*(sp4) + (11871773473/50000000000000 : ℝ)*(sp7) + (486532131853157/12500000000000 : ℝ)*(f.failure) + (7869808082526713/100000000000000 : ℝ)*(f.sum) + (376155441421/91000000000000000000000000 : ℝ)*base65 + (93509450742231/45500000000000000000000000000 : ℝ)*base68 + (116249930322231/45500000000000000000000000000 : ℝ)*base70 + (92004066355769/45500000000000000000000000000 : ℝ)*base71 + (11692696191/3640000000000000000000000 : ℝ)*base73 + (65098506271231/45500000000000000000000000000 : ℝ)*base76 + (407465540462231/45500000000000000000000000000 : ℝ)*base78 + (104299486128769/45500000000000000000000000000 : ℝ)*base79 + (168180056689/22750000000000000000000000 : ℝ)*base81 + (175089/312500000000000000000 : ℝ)*base90 + (175089/312500000000000000000 : ℝ)*base92 + (175089/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42291515829864612798876999/7280000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19987913/5000000000000 : ℝ)*(base19) + (533187017/50000000000000 : ℝ)*(base23) + (25839679/50000000000000 : ℝ)*(upper3) + (87869293/100000000000000 : ℝ)*(lower4) + (9123743/50000000000000 : ℝ)*(upper5) + (5911409164959121/100000000000000 : ℝ)*(major0) + (5911409164959121/100000000000000 : ℝ)*(major1) + (5911409164959121/100000000000000 : ℝ)*(major2) + (14012661463/100000000000000 : ℝ)*(sp1) + (16727242497/50000000000000 : ℝ)*(sp2) + (1582091395689593/20000000000000 : ℝ)*(sp4) + (3955221283014121/50000000000000 : ℝ)*(sp5) + (3955211228794469/50000000000000 : ℝ)*(sp6) + (978090289456949/25000000000000 : ℝ)*(sp7) + (978090289456949/25000000000000 : ℝ)*(f.failure) + (1582091395689593/20000000000000 : ℝ)*(f.sum) + (60120040088813/14560000000000000000000000000 : ℝ)*base66 + (91765881562661167/14560000000000000000000000000000 : ℝ)*base67 + (108836894852901167/14560000000000000000000000000000 : ℝ)*base69 + (48935372599898833/14560000000000000000000000000000 : ℝ)*base72 + (9847426789587/14560000000000000000000000000 : ℝ)*base73 + (367426960142821167/14560000000000000000000000000000 : ℝ)*base75 + (31644624934501167/14560000000000000000000000000000 : ℝ)*base77 + (129163546895258833/14560000000000000000000000000000 : ℝ)*base80 + (14834020560973/14560000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2909073/625000000000000000000 : ℝ)*base90 + (2909073/625000000000000000000 : ℝ)*base92 + (2909073/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1225_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11431/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1225_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1225_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (943/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11431/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1225_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1225_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1225_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8417/2048 : ℝ) ≤ p) (hpb : p ≤ (4209/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37773923/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (943/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11431/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1225_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

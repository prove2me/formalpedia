-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1394_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:43:55.134982+00:00
-- url     : https://prove2.me/submissions/c7eff83e-99ad-4032-9326-f37bcd7525cb

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
theorem support_rectangle_w1394_s6_0 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1999885927/10000000000 : ℝ)*x 0 + (216401187/400000000 : ℝ)*x 1 + (1049212689/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1999885927/10000000000 : ℝ)^2177 ≤ (2438310892471/20000000000000 : ℝ)^1665 := by
    have hnat : (1999885927 : ℕ)^2177*20000000000000^1665 ≤ 2438310892471^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999885927 10000000000 2438310892471 20000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216401187/400000000 : ℝ)^2177 ≤ (44787470573927/100000000000000 : ℝ)^1665 := by
    have hnat : (216401187 : ℕ)^2177*100000000000000^1665 ≤ 44787470573927^1665*400000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216401187 400000000 44787470573927 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049212689/2000000000 : ℝ)^2177 ≤ (43020974959527/100000000000000 : ℝ)^1665 := by
    have hnat : (1049212689 : ℕ)^2177*100000000000000^1665 ≤ 43020974959527^1665*2000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049212689 2000000000 43020974959527 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1999885927/10000000000 : ℝ), (216401187/400000000 : ℝ), (1049212689/2000000000 : ℝ)] ![(2438310892471/20000000000000 : ℝ), (44787470573927/100000000000000 : ℝ), (43020974959527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1999885927/10000000000 : ℝ)|^2177 ≤ (2438310892471/20000000000000 : ℝ)^1665
        have hw : |(-1999885927/10000000000 : ℝ)|=(1999885927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216401187/400000000 : ℝ)|^2177 ≤ (44787470573927/100000000000000 : ℝ)^1665
        have hw : |(216401187/400000000 : ℝ)|=(216401187/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049212689/2000000000 : ℝ)|^2177 ≤ (43020974959527/100000000000000 : ℝ)^1665
        have hw : |(1049212689/2000000000 : ℝ)|=(1049212689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s6_1 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348040103/10000000000 : ℝ)*x 0 + (-416677741/2000000000 : ℝ)*x 1 + (5246063441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348040103/10000000000 : ℝ)^2177 ≤ (44117660173739/100000000000000 : ℝ)^1665 := by
    have hnat : (5348040103 : ℕ)^2177*100000000000000^1665 ≤ 44117660173739^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348040103 10000000000 44117660173739 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416677741/2000000000 : ℝ)^2177 ≤ (12861364892733/100000000000000 : ℝ)^1665 := by
    have hnat : (416677741 : ℕ)^2177*100000000000000^1665 ≤ 12861364892733^1665*2000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416677741 2000000000 12861364892733 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246063441/10000000000 : ℝ)^2177 ≤ (21510487458319/50000000000000 : ℝ)^1665 := by
    have hnat : (5246063441 : ℕ)^2177*50000000000000^1665 ≤ 21510487458319^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246063441 10000000000 21510487458319 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348040103/10000000000 : ℝ), (-416677741/2000000000 : ℝ), (5246063441/10000000000 : ℝ)] ![(44117660173739/100000000000000 : ℝ), (12861364892733/100000000000000 : ℝ), (21510487458319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348040103/10000000000 : ℝ)|^2177 ≤ (44117660173739/100000000000000 : ℝ)^1665
        have hw : |(5348040103/10000000000 : ℝ)|=(5348040103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-416677741/2000000000 : ℝ)|^2177 ≤ (12861364892733/100000000000000 : ℝ)^1665
        have hw : |(-416677741/2000000000 : ℝ)|=(416677741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246063441/10000000000 : ℝ)|^2177 ≤ (21510487458319/50000000000000 : ℝ)^1665
        have hw : |(5246063441/10000000000 : ℝ)|=(5246063441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s6_2 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534803999/1000000000 : ℝ)*x 0 + (2623031821/5000000000 : ℝ)*x 1 + (-2083388589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534803999/1000000000 : ℝ)^2177 ≤ (44117658954917/100000000000000 : ℝ)^1665 := by
    have hnat : (534803999 : ℕ)^2177*100000000000000^1665 ≤ 44117658954917^1665*1000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534803999 1000000000 44117658954917 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623031821/5000000000 : ℝ)^2177 ≤ (21510488535917/50000000000000 : ℝ)^1665 := by
    have hnat : (2623031821 : ℕ)^2177*50000000000000^1665 ≤ 21510488535917^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623031821 5000000000 21510488535917 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083388589/10000000000 : ℝ)^2177 ≤ (1607670494553/12500000000000 : ℝ)^1665 := by
    have hnat : (2083388589 : ℕ)^2177*12500000000000^1665 ≤ 1607670494553^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083388589 10000000000 1607670494553 12500000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534803999/1000000000 : ℝ), (2623031821/5000000000 : ℝ), (-2083388589/10000000000 : ℝ)] ![(44117658954917/100000000000000 : ℝ), (21510488535917/50000000000000 : ℝ), (1607670494553/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534803999/1000000000 : ℝ)|^2177 ≤ (44117658954917/100000000000000 : ℝ)^1665
        have hw : |(534803999/1000000000 : ℝ)|=(534803999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623031821/5000000000 : ℝ)|^2177 ≤ (21510488535917/50000000000000 : ℝ)^1665
        have hw : |(2623031821/5000000000 : ℝ)|=(2623031821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2083388589/10000000000 : ℝ)|^2177 ≤ (1607670494553/12500000000000 : ℝ)^1665
        have hw : |(-2083388589/10000000000 : ℝ)|=(2083388589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s6_3 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (269575171/625000000 : ℝ)*x 0 + (2070682077/5000000000 : ℝ)*x 1 + (2245766863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269575171/625000000 : ℝ)^2177 ≤ (6660825966461/20000000000000 : ℝ)^1665 := by
    have hnat : (269575171 : ℕ)^2177*20000000000000^1665 ≤ 6660825966461^1665*625000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269575171 625000000 6660825966461 20000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070682077/5000000000 : ℝ)^2177 ≤ (3947500198227/12500000000000 : ℝ)^1665 := by
    have hnat : (2070682077 : ℕ)^2177*12500000000000^1665 ≤ 3947500198227^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070682077 5000000000 3947500198227 12500000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245766863/5000000000 : ℝ)^2177 ≤ (35115868571049/100000000000000 : ℝ)^1665 := by
    have hnat : (2245766863 : ℕ)^2177*100000000000000^1665 ≤ 35115868571049^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245766863 5000000000 35115868571049 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269575171/625000000 : ℝ), (2070682077/5000000000 : ℝ), (2245766863/5000000000 : ℝ)] ![(6660825966461/20000000000000 : ℝ), (3947500198227/12500000000000 : ℝ), (35115868571049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269575171/625000000 : ℝ)|^2177 ≤ (6660825966461/20000000000000 : ℝ)^1665
        have hw : |(269575171/625000000 : ℝ)|=(269575171/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2070682077/5000000000 : ℝ)|^2177 ≤ (3947500198227/12500000000000 : ℝ)^1665
        have hw : |(2070682077/5000000000 : ℝ)|=(2070682077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245766863/5000000000 : ℝ)|^2177 ≤ (35115868571049/100000000000000 : ℝ)^1665
        have hw : |(2245766863/5000000000 : ℝ)|=(2245766863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s6_4 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1999897789/10000000000 : ℝ)*x 0 + (327915821/625000000 : ℝ)*x 1 + (5409436783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1999897789/10000000000 : ℝ)^2177 ≤ (1219164901123/10000000000000 : ℝ)^1665 := by
    have hnat : (1999897789 : ℕ)^2177*10000000000000^1665 ≤ 1219164901123^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999897789 10000000000 1219164901123 10000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327915821/625000000 : ℝ)^2177 ≤ (43027297955513/100000000000000 : ℝ)^1665 := by
    have hnat : (327915821 : ℕ)^2177*100000000000000^1665 ≤ 43027297955513^1665*625000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327915821 625000000 43027297955513 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409436783/10000000000 : ℝ)^2177 ≤ (44781053022583/100000000000000 : ℝ)^1665 := by
    have hnat : (5409436783 : ℕ)^2177*100000000000000^1665 ≤ 44781053022583^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409436783 10000000000 44781053022583 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1999897789/10000000000 : ℝ), (327915821/625000000 : ℝ), (5409436783/10000000000 : ℝ)] ![(1219164901123/10000000000000 : ℝ), (43027297955513/100000000000000 : ℝ), (44781053022583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1999897789/10000000000 : ℝ)|^2177 ≤ (1219164901123/10000000000000 : ℝ)^1665
        have hw : |(-1999897789/10000000000 : ℝ)|=(1999897789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327915821/625000000 : ℝ)|^2177 ≤ (43027297955513/100000000000000 : ℝ)^1665
        have hw : |(327915821/625000000 : ℝ)|=(327915821/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409436783/10000000000 : ℝ)|^2177 ≤ (44781053022583/100000000000000 : ℝ)^1665
        have hw : |(5409436783/10000000000 : ℝ)|=(5409436783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s6_5 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (212222563/400000000 : ℝ)*x 0 + (-960007713/5000000000 : ℝ)*x 1 + (5409436799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212222563/400000000 : ℝ)^2177 ≤ (10915018140403/25000000000000 : ℝ)^1665 := by
    have hnat : (212222563 : ℕ)^2177*25000000000000^1665 ≤ 10915018140403^1665*400000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212222563 400000000 10915018140403 25000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960007713/5000000000 : ℝ)^2177 ≤ (11558874226719/100000000000000 : ℝ)^1665 := by
    have hnat : (960007713 : ℕ)^2177*100000000000000^1665 ≤ 11558874226719^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960007713 5000000000 11558874226719 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409436799/10000000000 : ℝ)^2177 ≤ (22390526597883/50000000000000 : ℝ)^1665 := by
    have hnat : (5409436799 : ℕ)^2177*50000000000000^1665 ≤ 22390526597883^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409436799 10000000000 22390526597883 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212222563/400000000 : ℝ), (-960007713/5000000000 : ℝ), (5409436799/10000000000 : ℝ)] ![(10915018140403/25000000000000 : ℝ), (11558874226719/100000000000000 : ℝ), (22390526597883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212222563/400000000 : ℝ)|^2177 ≤ (10915018140403/25000000000000 : ℝ)^1665
        have hw : |(212222563/400000000 : ℝ)|=(212222563/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-960007713/5000000000 : ℝ)|^2177 ≤ (11558874226719/100000000000000 : ℝ)^1665
        have hw : |(-960007713/5000000000 : ℝ)|=(960007713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409436799/10000000000 : ℝ)|^2177 ≤ (22390526597883/50000000000000 : ℝ)^1665
        have hw : |(5409436799/10000000000 : ℝ)|=(5409436799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s6_6 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (663195473/1250000000 : ℝ)*x 0 + (270471851/500000000 : ℝ)*x 1 + (-12000097/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663195473/1250000000 : ℝ)^2177 ≤ (43660069430561/100000000000000 : ℝ)^1665 := by
    have hnat : (663195473 : ℕ)^2177*100000000000000^1665 ≤ 43660069430561^1665*1250000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663195473 1250000000 43660069430561 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270471851/500000000 : ℝ)^2177 ≤ (44781055587863/100000000000000 : ℝ)^1665 := by
    have hnat : (270471851 : ℕ)^2177*100000000000000^1665 ≤ 44781055587863^1665*500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270471851 500000000 44781055587863 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12000097/62500000 : ℝ)^2177 ≤ (2889718741659/25000000000000 : ℝ)^1665 := by
    have hnat : (12000097 : ℕ)^2177*25000000000000^1665 ≤ 2889718741659^1665*62500000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12000097 62500000 2889718741659 25000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663195473/1250000000 : ℝ), (270471851/500000000 : ℝ), (-12000097/62500000 : ℝ)] ![(43660069430561/100000000000000 : ℝ), (44781055587863/100000000000000 : ℝ), (2889718741659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663195473/1250000000 : ℝ)|^2177 ≤ (43660069430561/100000000000000 : ℝ)^1665
        have hw : |(663195473/1250000000 : ℝ)|=(663195473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270471851/500000000 : ℝ)|^2177 ≤ (44781055587863/100000000000000 : ℝ)^1665
        have hw : |(270471851/500000000 : ℝ)|=(270471851/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12000097/62500000 : ℝ)|^2177 ≤ (2889718741659/25000000000000 : ℝ)^1665
        have hw : |(-12000097/62500000 : ℝ)|=(12000097/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s6_7 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (43132281/100000000 : ℝ)*x 0 + (4490274333/10000000000 : ℝ)*x 1 + (2071314789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43132281/100000000 : ℝ)^2177 ≤ (33304385903393/100000000000000 : ℝ)^1665 := by
    have hnat : (43132281 : ℕ)^2177*100000000000000^1665 ≤ 33304385903393^1665*100000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43132281 100000000 33304385903393 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490274333/10000000000 : ℝ)^2177 ≤ (4387874388127/12500000000000 : ℝ)^1665 := by
    have hnat : (4490274333 : ℕ)^2177*12500000000000^1665 ≤ 4387874388127^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490274333 10000000000 4387874388127 12500000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2071314789/5000000000 : ℝ)^2177 ≤ (15796309485873/50000000000000 : ℝ)^1665 := by
    have hnat : (2071314789 : ℕ)^2177*50000000000000^1665 ≤ 15796309485873^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071314789 5000000000 15796309485873 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43132281/100000000 : ℝ), (4490274333/10000000000 : ℝ), (2071314789/5000000000 : ℝ)] ![(33304385903393/100000000000000 : ℝ), (4387874388127/12500000000000 : ℝ), (15796309485873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43132281/100000000 : ℝ)|^2177 ≤ (33304385903393/100000000000000 : ℝ)^1665
        have hw : |(43132281/100000000 : ℝ)|=(43132281/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490274333/10000000000 : ℝ)|^2177 ≤ (4387874388127/12500000000000 : ℝ)^1665
        have hw : |(4490274333/10000000000 : ℝ)|=(4490274333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2071314789/5000000000 : ℝ)|^2177 ≤ (15796309485873/50000000000000 : ℝ)^1665
        have hw : |(2071314789/5000000000 : ℝ)|=(2071314789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1394_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156781207/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5633/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7369/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11261/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11261/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11261/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11261/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11261/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11261/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11261/100000 : ℝ) ^ (4353/1024 : ℝ) ≤ (9295566863761549/100000000000000000000 : ℝ) := by
    have hpowers : (11261/100000 : ℝ)^4353 ≤ (9295566863761549/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11261 : ℕ)^4353*100000000000000000000^1024 ≤ 9295566863761549^1024*100000^4353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11261 100000 9295566863761549 100000000000000000000 4353 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11261/100000 : ℝ)) (X := (9295566863761549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14743/100000 : ℝ) ^ (4353/1024 : ℝ) ≤ (730496281133183/2500000000000000000 : ℝ) := by
    have hpowers : (14743/100000 : ℝ)^4353 ≤ (730496281133183/2500000000000000000 : ℝ)^1024 := by
      have hnat : (14743 : ℕ)^4353*2500000000000000000^1024 ≤ 730496281133183^1024*100000^4353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14743 100000 730496281133183 2500000000000000000 4353 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14743/100000 : ℝ)) (X := (730496281133183/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009295566863761549/50000000000000000000 : ℝ) ≤ (5000218653431487/5000000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (50009295566863761549/50000000000000000000 : ℝ)^1024 ≤ (5000218653431487/5000000000000000 : ℝ)^4353 := by
      have hnat : (50009295566863761549 : ℕ)^1024*5000000000000000^4353 ≤ 5000218653431487^4353*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009295566863761549 50000000000000000000 5000218653431487 5000000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000218653431487/5000000000000000 : ℝ)) (X := (50009295566863761549/50000000000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038515418109088869/100000000000000000000 : ℝ) ≤ (2500226475884189/2500000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (100038515418109088869/100000000000000000000 : ℝ)^1024 ≤ (2500226475884189/2500000000000000 : ℝ)^4353 := by
      have hnat : (100038515418109088869 : ℕ)^1024*2500000000000000^4353 ≤ 2500226475884189^4353*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038515418109088869 100000000000000000000 2500226475884189 2500000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500226475884189/2500000000000000 : ℝ)) (X := (100038515418109088869/100000000000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250730496281133183/1250000000000000000 : ℝ) ≤ (5000687250105269/5000000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (1250730496281133183/1250000000000000000 : ℝ)^1024 ≤ (5000687250105269/5000000000000000 : ℝ)^4353 := by
      have hnat : (1250730496281133183 : ℕ)^1024*5000000000000000^4353 ≤ 5000687250105269^4353*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250730496281133183 1250000000000000000 5000687250105269 5000000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000687250105269/5000000000000000 : ℝ)) (X := (1250730496281133183/1250000000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9295566863761549/100000000000000000000 : ℝ) ≤ ((2175685560513122329/2176250000000000000 : ℝ)+2*(234298336891/174100000000000 : ℝ)*(11261/100000 : ℝ))^(4353/1024 : ℝ) := by
    rw [show (2175685560513122329/2176250000000000000 : ℝ)+2*(234298336891/174100000000000 : ℝ)*(11261/100000 : ℝ)=(5000218653431487/5000000000000000 : ℝ) by norm_num, show 1+2*(9295566863761549/100000000000000000000 : ℝ)=(50009295566863761549/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(730496281133183/2500000000000000000 : ℝ)+(9295566863761549/100000000000000000000 : ℝ) ≤ ((2175685560513122329/2176250000000000000 : ℝ)+(234298336891/174100000000000 : ℝ)*((14743/100000 : ℝ)+(11261/100000 : ℝ)))^(4353/1024 : ℝ) := by
    rw [show (2175685560513122329/2176250000000000000 : ℝ)+(234298336891/174100000000000 : ℝ)*((14743/100000 : ℝ)+(11261/100000 : ℝ))=(2500226475884189/2500000000000000 : ℝ) by norm_num, show 1+(730496281133183/2500000000000000000 : ℝ)+(9295566863761549/100000000000000000000 : ℝ)=(100038515418109088869/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(730496281133183/2500000000000000000 : ℝ) ≤ ((2175685560513122329/2176250000000000000 : ℝ)+2*(234298336891/174100000000000 : ℝ)*(14743/100000 : ℝ))^(4353/1024 : ℝ) := by
    rw [show (2175685560513122329/2176250000000000000 : ℝ)+2*(234298336891/174100000000000 : ℝ)*(14743/100000 : ℝ)=(5000687250105269/5000000000000000 : ℝ) by norm_num, show 1+2*(730496281133183/2500000000000000000 : ℝ)=(1250730496281133183/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2175685560513122329/2176250000000000000 : ℝ)*(X 1 0+X 2 0)+(234298336891/174100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (11261/100000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (2175685560513122329/2176250000000000000 : ℝ)) (alpha := (234298336891/174100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2175685560513122329/2176250000000000000 : ℝ)*(X 0 1+X 2 1)+(234298336891/174100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (11261/100000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (2175685560513122329/2176250000000000000 : ℝ)) (alpha := (234298336891/174100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2175685560513122329/2176250000000000000 : ℝ)*(X 0 2+X 1 2)+(234298336891/174100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (11261/100000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (2175685560513122329/2176250000000000000 : ℝ)) (alpha := (234298336891/174100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1999885927/10000000000 : ℝ)*X 0 0+(216401187/400000000 : ℝ)*X 0 1+(1049212689/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348040103/10000000000 : ℝ)*X 1 0+(-416677741/2000000000 : ℝ)*X 1 1+(5246063441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534803999/1000000000 : ℝ)*X 2 0+(2623031821/5000000000 : ℝ)*X 2 1+(-2083388589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((269575171/625000000 : ℝ)*X 0 0+(2070682077/5000000000 : ℝ)*X 0 1+(2245766863/5000000000 : ℝ)*X 0 2+(269575171/625000000 : ℝ)*X 1 0+(2070682077/5000000000 : ℝ)*X 1 1+(2245766863/5000000000 : ℝ)*X 1 2+(269575171/625000000 : ℝ)*X 2 0+(2070682077/5000000000 : ℝ)*X 2 1+(2245766863/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1999897789/10000000000 : ℝ)*X 0 0+(327915821/625000000 : ℝ)*X 0 1+(5409436783/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212222563/400000000 : ℝ)*X 1 0+(-960007713/5000000000 : ℝ)*X 1 1+(5409436799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663195473/1250000000 : ℝ)*X 2 0+(270471851/500000000 : ℝ)*X 2 1+(-12000097/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((43132281/100000000 : ℝ)*X 0 0+(4490274333/10000000000 : ℝ)*X 0 1+(2071314789/5000000000 : ℝ)*X 0 2+(43132281/100000000 : ℝ)*X 1 0+(4490274333/10000000000 : ℝ)*X 1 1+(2071314789/5000000000 : ℝ)*X 1 2+(43132281/100000000 : ℝ)*X 2 0+(4490274333/10000000000 : ℝ)*X 2 1+(2071314789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (451062219862804267825168803/54406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (171552811/12500000000000 : ℝ)*(base19) + (246875187/20000000000000 : ℝ)*(base23) + (4910399/100000000000000 : ℝ)*(lower2) + (14281859/100000000000000 : ℝ)*(upper3) + (65494401/50000000000000 : ℝ)*(upper5) + (2238669886809723/50000000000000 : ℝ)*(major0) + (2238669886809723/50000000000000 : ℝ)*(major1) + (2238669886809723/50000000000000 : ℝ)*(major2) + (6098851798885583/100000000000000 : ℝ)*(sp0) + (3049444669268133/50000000000000 : ℝ)*(sp1) + (6098889476582819/100000000000000 : ℝ)*(sp2) + (1427887465436107/50000000000000 : ℝ)*(sp3) + (38912073171/100000000000000 : ℝ)*(sp4) + (1703631687/12500000000000 : ℝ)*(sp7) + (285578855992571/10000000000000 : ℝ)*(f.failure) + (3049445355479377/50000000000000 : ℝ)*(f.sum) + (5372014390433/4352500000000000000000000000 : ℝ)*base65 + (1876276341139795133/108812500000000000000000000000000 : ℝ)*base68 + (2827932128513232633/108812500000000000000000000000000 : ℝ)*base70 + (1865837478913357633/108812500000000000000000000000000 : ℝ)*base72 + (6193806252077/1088125000000000000000000000 : ℝ)*base73 + (3350949091681857633/108812500000000000000000000000000 : ℝ)*base76 + (1938856804744107633/108812500000000000000000000000000 : ℝ)*base78 + (1909951309052107633/108812500000000000000000000000000 : ℝ)*base80 + (31088161376619/8705000000000000000000000000 : ℝ)*base82 + (4413197/1000000000000000000000 : ℝ)*base89 + (4413197/1000000000000000000000 : ℝ)*base91 + (4413197/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3287772396591733605219/1088125000000000000000000000 : ℝ) := by norm_num
    linear_combination (166348997/25000000000000 : ℝ)*(base19) + (169344437/50000000000000 : ℝ)*(base23) + (21586241/100000000000000 : ℝ)*(upper2) + (108119833/100000000000000 : ℝ)*(upper3) + (9219959/10000000000000 : ℝ)*(upper5) + (2254904442859763/50000000000000 : ℝ)*(major0) + (2254904442859763/50000000000000 : ℝ)*(major1) + (2254904442859763/50000000000000 : ℝ)*(major2) + (12680365711/100000000000000 : ℝ)*(sp1) + (4438146527/50000000000000 : ℝ)*(sp2) + (1535779821688733/25000000000000 : ℝ)*(sp4) + (6143105940993233/100000000000000 : ℝ)*(sp5) + (6143110071773003/100000000000000 : ℝ)*(sp6) + (2876498383967363/100000000000000 : ℝ)*(sp7) + (2876498383967363/100000000000000 : ℝ)*(f.failure) + (1535779821688733/25000000000000 : ℝ)*(f.sum) + (2190216238253/4352500000000000000000000000 : ℝ)*base65 + (1208636636810673027/108812500000000000000000000000000 : ℝ)*base67 + (548605363176764473/108812500000000000000000000000000 : ℝ)*base70 + (793497299961639473/108812500000000000000000000000000 : ℝ)*base72 + (14114670828159/2176250000000000000000000000 : ℝ)*base73 + (722347600395610527/108812500000000000000000000000000 : ℝ)*base75 + (921889532528139473/108812500000000000000000000000000 : ℝ)*base78 + (1366409650234673027/108812500000000000000000000000000 : ℝ)*base79 + (14641077520587/4352500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (19747141/10000000000000000000000 : ℝ)*base89 + (19747141/10000000000000000000000 : ℝ)*base91 + (19747141/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1394_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156781207/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1394_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1394_s7_0 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1999889567/10000000000 : ℝ)*x 0 + (540999169/1000000000 : ℝ)*x 1 + (1049219817/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1999889567/10000000000 : ℝ)^2177 ≤ (12191583475817/100000000000000 : ℝ)^1665 := by
    have hnat : (1999889567 : ℕ)^2177*100000000000000^1665 ≤ 12191583475817^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999889567 10000000000 12191583475817 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540999169/1000000000 : ℝ)^2177 ≤ (44787059412143/100000000000000 : ℝ)^1665 := by
    have hnat : (540999169 : ℕ)^2177*100000000000000^1665 ≤ 44787059412143^1665*1000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540999169 1000000000 44787059412143 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049219817/2000000000 : ℝ)^2177 ≤ (43021357105291/100000000000000 : ℝ)^1665 := by
    have hnat : (1049219817 : ℕ)^2177*100000000000000^1665 ≤ 43021357105291^1665*2000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049219817 2000000000 43021357105291 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1999889567/10000000000 : ℝ), (540999169/1000000000 : ℝ), (1049219817/2000000000 : ℝ)] ![(12191583475817/100000000000000 : ℝ), (44787059412143/100000000000000 : ℝ), (43021357105291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1999889567/10000000000 : ℝ)|^2177 ≤ (12191583475817/100000000000000 : ℝ)^1665
        have hw : |(-1999889567/10000000000 : ℝ)|=(1999889567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540999169/1000000000 : ℝ)|^2177 ≤ (44787059412143/100000000000000 : ℝ)^1665
        have hw : |(540999169/1000000000 : ℝ)|=(540999169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049219817/2000000000 : ℝ)|^2177 ≤ (43021357105291/100000000000000 : ℝ)^1665
        have hw : |(1049219817/2000000000 : ℝ)|=(1049219817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s7_1 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348030389/10000000000 : ℝ)*x 0 + (-2083354247/10000000000 : ℝ)*x 1 + (327881197/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348030389/10000000000 : ℝ)^2177 ≤ (44117555398181/100000000000000 : ℝ)^1665 := by
    have hnat : (5348030389 : ℕ)^2177*100000000000000^1665 ≤ 44117555398181^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348030389 10000000000 44117555398181 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2083354247/10000000000 : ℝ)^2177 ≤ (2572217352281/20000000000000 : ℝ)^1665 := by
    have hnat : (2083354247 : ℕ)^2177*20000000000000^1665 ≤ 2572217352281^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083354247 10000000000 2572217352281 20000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327881197/625000000 : ℝ)^2177 ≤ (10755339455923/25000000000000 : ℝ)^1665 := by
    have hnat : (327881197 : ℕ)^2177*25000000000000^1665 ≤ 10755339455923^1665*625000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327881197 625000000 10755339455923 25000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348030389/10000000000 : ℝ), (-2083354247/10000000000 : ℝ), (327881197/625000000 : ℝ)] ![(44117555398181/100000000000000 : ℝ), (2572217352281/20000000000000 : ℝ), (10755339455923/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348030389/10000000000 : ℝ)|^2177 ≤ (44117555398181/100000000000000 : ℝ)^1665
        have hw : |(5348030389/10000000000 : ℝ)|=(5348030389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2083354247/10000000000 : ℝ)|^2177 ≤ (2572217352281/20000000000000 : ℝ)^1665
        have hw : |(-2083354247/10000000000 : ℝ)|=(2083354247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327881197/625000000 : ℝ)|^2177 ≤ (10755339455923/25000000000000 : ℝ)^1665
        have hw : |(327881197/625000000 : ℝ)|=(327881197/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s7_2 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069606099/2000000000 : ℝ)*x 0 + (5246099253/10000000000 : ℝ)*x 1 + (-520838493/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069606099/2000000000 : ℝ)^2177 ≤ (88235113083/200000000000 : ℝ)^1665 := by
    have hnat : (1069606099 : ℕ)^2177*200000000000^1665 ≤ 88235113083^1665*2000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069606099 2000000000 88235113083 200000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246099253/10000000000 : ℝ)^2177 ≤ (21510679453327/50000000000000 : ℝ)^1665 := by
    have hnat : (5246099253 : ℕ)^2177*50000000000000^1665 ≤ 21510679453327^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246099253 10000000000 21510679453327 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520838493/2500000000 : ℝ)^2177 ≤ (321527113543/2500000000000 : ℝ)^1665 := by
    have hnat : (520838493 : ℕ)^2177*2500000000000^1665 ≤ 321527113543^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520838493 2500000000 321527113543 2500000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069606099/2000000000 : ℝ), (5246099253/10000000000 : ℝ), (-520838493/2500000000 : ℝ)] ![(88235113083/200000000000 : ℝ), (21510679453327/50000000000000 : ℝ), (321527113543/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069606099/2000000000 : ℝ)|^2177 ≤ (88235113083/200000000000 : ℝ)^1665
        have hw : |(1069606099/2000000000 : ℝ)|=(1069606099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246099253/10000000000 : ℝ)|^2177 ≤ (21510679453327/50000000000000 : ℝ)^1665
        have hw : |(5246099253/10000000000 : ℝ)|=(5246099253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-520838493/2500000000 : ℝ)|^2177 ≤ (321527113543/2500000000000 : ℝ)^1665
        have hw : |(-520838493/2500000000 : ℝ)|=(520838493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s7_3 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2156602751/5000000000 : ℝ)*x 0 + (1035360643/2500000000 : ℝ)*x 1 + (1122863627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156602751/5000000000 : ℝ)^2177 ≤ (16652078878699/50000000000000 : ℝ)^1665 := by
    have hnat : (2156602751 : ℕ)^2177*50000000000000^1665 ≤ 16652078878699^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156602751 5000000000 16652078878699 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035360643/2500000000 : ℝ)^2177 ≤ (15790391723763/50000000000000 : ℝ)^1665 := by
    have hnat : (1035360643 : ℕ)^2177*50000000000000^1665 ≤ 15790391723763^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035360643 2500000000 15790391723763 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122863627/2500000000 : ℝ)^2177 ≤ (35115058775031/100000000000000 : ℝ)^1665 := by
    have hnat : (1122863627 : ℕ)^2177*100000000000000^1665 ≤ 35115058775031^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122863627 2500000000 35115058775031 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2156602751/5000000000 : ℝ), (1035360643/2500000000 : ℝ), (1122863627/2500000000 : ℝ)] ![(16652078878699/50000000000000 : ℝ), (15790391723763/50000000000000 : ℝ), (35115058775031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2156602751/5000000000 : ℝ)|^2177 ≤ (16652078878699/50000000000000 : ℝ)^1665
        have hw : |(2156602751/5000000000 : ℝ)|=(2156602751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035360643/2500000000 : ℝ)|^2177 ≤ (15790391723763/50000000000000 : ℝ)^1665
        have hw : |(1035360643/2500000000 : ℝ)|=(1035360643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122863627/2500000000 : ℝ)|^2177 ≤ (35115058775031/100000000000000 : ℝ)^1665
        have hw : |(1122863627/2500000000 : ℝ)|=(1122863627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s7_4 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-999950581/5000000000 : ℝ)*x 0 + (5246688389/10000000000 : ℝ)*x 1 + (8655039/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (999950581/5000000000 : ℝ)^2177 ≤ (2438335179311/20000000000000 : ℝ)^1665 := by
    have hnat : (999950581 : ℕ)^2177*20000000000000^1665 ≤ 2438335179311^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999950581 5000000000 2438335179311 20000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246688389/10000000000 : ℝ)^2177 ≤ (1721107038591/4000000000000 : ℝ)^1665 := by
    have hnat : (5246688389 : ℕ)^2177*4000000000000^1665 ≤ 1721107038591^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246688389 10000000000 1721107038591 4000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8655039/16000000 : ℝ)^2177 ≤ (44780648120071/100000000000000 : ℝ)^1665 := by
    have hnat : (8655039 : ℕ)^2177*100000000000000^1665 ≤ 44780648120071^1665*16000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8655039 16000000 44780648120071 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-999950581/5000000000 : ℝ), (5246688389/10000000000 : ℝ), (8655039/16000000 : ℝ)] ![(2438335179311/20000000000000 : ℝ), (1721107038591/4000000000000 : ℝ), (44780648120071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-999950581/5000000000 : ℝ)|^2177 ≤ (2438335179311/20000000000000 : ℝ)^1665
        have hw : |(-999950581/5000000000 : ℝ)|=(999950581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246688389/10000000000 : ℝ)|^2177 ≤ (1721107038591/4000000000000 : ℝ)^1665
        have hw : |(5246688389/10000000000 : ℝ)|=(5246688389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8655039/16000000 : ℝ)|^2177 ≤ (44780648120071/100000000000000 : ℝ)^1665
        have hw : |(8655039/16000000 : ℝ)|=(8655039/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s7_5 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305573263/10000000000 : ℝ)*x 0 + (-96002709/500000000 : ℝ)*x 1 + (5409399483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305573263/10000000000 : ℝ)^2177 ≤ (2183008571053/5000000000000 : ℝ)^1665 := by
    have hnat : (5305573263 : ℕ)^2177*5000000000000^1665 ≤ 2183008571053^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305573263 10000000000 2183008571053 5000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96002709/500000000 : ℝ)^2177 ≤ (11559179278029/100000000000000 : ℝ)^1665 := by
    have hnat : (96002709 : ℕ)^2177*100000000000000^1665 ≤ 11559179278029^1665*500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96002709 500000000 11559179278029 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409399483/10000000000 : ℝ)^2177 ≤ (44780649289057/100000000000000 : ℝ)^1665 := by
    have hnat : (5409399483 : ℕ)^2177*100000000000000^1665 ≤ 44780649289057^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409399483 10000000000 44780649289057 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305573263/10000000000 : ℝ), (-96002709/500000000 : ℝ), (5409399483/10000000000 : ℝ)] ![(2183008571053/5000000000000 : ℝ), (11559179278029/100000000000000 : ℝ), (44780649289057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305573263/10000000000 : ℝ)|^2177 ≤ (2183008571053/5000000000000 : ℝ)^1665
        have hw : |(5305573263/10000000000 : ℝ)|=(5305573263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-96002709/500000000 : ℝ)|^2177 ≤ (11559179278029/100000000000000 : ℝ)^1665
        have hw : |(-96002709/500000000 : ℝ)|=(96002709/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409399483/10000000000 : ℝ)|^2177 ≤ (44780649289057/100000000000000 : ℝ)^1665
        have hw : |(5409399483/10000000000 : ℝ)|=(5409399483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s7_6 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4313230593/10000000000 : ℝ)*x 0 + (89803927/200000000 : ℝ)*x 1 + (4142706993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313230593/10000000000 : ℝ)^2177 ≤ (33304411072367/100000000000000 : ℝ)^1665 := by
    have hnat : (4313230593 : ℕ)^2177*100000000000000^1665 ≤ 33304411072367^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313230593 10000000000 33304411072367 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89803927/200000000 : ℝ)^2177 ≤ (17551099001169/50000000000000 : ℝ)^1665 := by
    have hnat : (89803927 : ℕ)^2177*50000000000000^1665 ≤ 17551099001169^1665*200000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89803927 200000000 17551099001169 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4142706993/10000000000 : ℝ)^2177 ≤ (6318678181119/20000000000000 : ℝ)^1665 := by
    have hnat : (4142706993 : ℕ)^2177*20000000000000^1665 ≤ 6318678181119^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142706993 10000000000 6318678181119 20000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313230593/10000000000 : ℝ), (89803927/200000000 : ℝ), (4142706993/10000000000 : ℝ)] ![(33304411072367/100000000000000 : ℝ), (17551099001169/50000000000000 : ℝ), (6318678181119/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313230593/10000000000 : ℝ)|^2177 ≤ (33304411072367/100000000000000 : ℝ)^1665
        have hw : |(4313230593/10000000000 : ℝ)|=(4313230593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(89803927/200000000 : ℝ)|^2177 ≤ (17551099001169/50000000000000 : ℝ)^1665
        have hw : |(89803927/200000000 : ℝ)|=(89803927/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4142706993/10000000000 : ℝ)|^2177 ≤ (6318678181119/20000000000000 : ℝ)^1665
        have hw : |(4142706993/10000000000 : ℝ)|=(4142706993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1394_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156781207/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11267/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7369/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7369/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5633/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7369/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5633/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7369/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5633/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7369/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5633/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7369/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5633/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7369/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5633/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5633/50000 : ℝ) ^ (4353/1024 : ℝ) ≤ (1862624940627941/20000000000000000000 : ℝ) := by
    have hpowers : (5633/50000 : ℝ)^4353 ≤ (1862624940627941/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5633 : ℕ)^4353*20000000000000000000^1024 ≤ 1862624940627941^1024*50000^4353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5633 50000 1862624940627941 20000000000000000000 4353 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5633/50000 : ℝ)) (X := (1862624940627941/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7369/50000 : ℝ) ^ (4353/1024 : ℝ) ≤ (29177748401669829/100000000000000000000 : ℝ) := by
    have hpowers : (7369/50000 : ℝ)^4353 ≤ (29177748401669829/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7369 : ℕ)^4353*100000000000000000000^1024 ≤ 29177748401669829^1024*50000^4353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7369 50000 29177748401669829 100000000000000000000 4353 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7369/50000 : ℝ)) (X := (29177748401669829/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001862624940627941/10000000000000000000 : ℝ) ≤ (1250054766600861/1250000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (10001862624940627941/10000000000000000000 : ℝ)^1024 ≤ (1250054766600861/1250000000000000 : ℝ)^4353 := by
      have hnat : (10001862624940627941 : ℕ)^1024*1250000000000000^4353 ≤ 1250054766600861^4353*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001862624940627941 10000000000000000000 1250054766600861 1250000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250054766600861/1250000000000000 : ℝ)) (X := (10001862624940627941/10000000000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019245436552404767/50000000000000000000 : ℝ) ≤ (5000452663154939/5000000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (50019245436552404767/50000000000000000000 : ℝ)^1024 ≤ (5000452663154939/5000000000000000 : ℝ)^4353 := by
      have hnat : (50019245436552404767 : ℕ)^1024*5000000000000000^4353 ≤ 5000452663154939^4353*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019245436552404767 50000000000000000000 5000452663154939 5000000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000452663154939/5000000000000000 : ℝ)) (X := (50019245436552404767/50000000000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029177748401669829/50000000000000000000 : ℝ) ≤ (2500343129953217/2500000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (50029177748401669829/50000000000000000000 : ℝ)^1024 ≤ (2500343129953217/2500000000000000 : ℝ)^4353 := by
      have hnat : (50029177748401669829 : ℕ)^1024*2500000000000000^4353 ≤ 2500343129953217^4353*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029177748401669829 50000000000000000000 2500343129953217 2500000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500343129953217/2500000000000000 : ℝ)) (X := (50029177748401669829/50000000000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1862624940627941/20000000000000000000 : ℝ) ≤ ((4338874299137018057/4340000000000000000 : ℝ)+2*(46719350299/34720000000000 : ℝ)*(5633/50000 : ℝ))^(4353/1024 : ℝ) := by
    rw [show (4338874299137018057/4340000000000000000 : ℝ)+2*(46719350299/34720000000000 : ℝ)*(5633/50000 : ℝ)=(1250054766600861/1250000000000000 : ℝ) by norm_num, show 1+2*(1862624940627941/20000000000000000000 : ℝ)=(10001862624940627941/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29177748401669829/100000000000000000000 : ℝ)+(1862624940627941/20000000000000000000 : ℝ) ≤ ((4338874299137018057/4340000000000000000 : ℝ)+(46719350299/34720000000000 : ℝ)*((7369/50000 : ℝ)+(5633/50000 : ℝ)))^(4353/1024 : ℝ) := by
    rw [show (4338874299137018057/4340000000000000000 : ℝ)+(46719350299/34720000000000 : ℝ)*((7369/50000 : ℝ)+(5633/50000 : ℝ))=(5000452663154939/5000000000000000 : ℝ) by norm_num, show 1+(29177748401669829/100000000000000000000 : ℝ)+(1862624940627941/20000000000000000000 : ℝ)=(50019245436552404767/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29177748401669829/100000000000000000000 : ℝ) ≤ ((4338874299137018057/4340000000000000000 : ℝ)+2*(46719350299/34720000000000 : ℝ)*(7369/50000 : ℝ))^(4353/1024 : ℝ) := by
    rw [show (4338874299137018057/4340000000000000000 : ℝ)+2*(46719350299/34720000000000 : ℝ)*(7369/50000 : ℝ)=(2500343129953217/2500000000000000 : ℝ) by norm_num, show 1+2*(29177748401669829/100000000000000000000 : ℝ)=(50029177748401669829/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4338874299137018057/4340000000000000000 : ℝ)*(X 1 0+X 2 0)+(46719350299/34720000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (5633/50000 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (4338874299137018057/4340000000000000000 : ℝ)) (alpha := (46719350299/34720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4338874299137018057/4340000000000000000 : ℝ)*(X 0 1+X 2 1)+(46719350299/34720000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (5633/50000 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (4338874299137018057/4340000000000000000 : ℝ)) (alpha := (46719350299/34720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4338874299137018057/4340000000000000000 : ℝ)*(X 0 2+X 1 2)+(46719350299/34720000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (5633/50000 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (4338874299137018057/4340000000000000000 : ℝ)) (alpha := (46719350299/34720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1999889567/10000000000 : ℝ)*X 0 0+(540999169/1000000000 : ℝ)*X 0 1+(1049219817/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348030389/10000000000 : ℝ)*X 1 0+(-2083354247/10000000000 : ℝ)*X 1 1+(327881197/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069606099/2000000000 : ℝ)*X 2 0+(5246099253/10000000000 : ℝ)*X 2 1+(-520838493/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2156602751/5000000000 : ℝ)*X 0 0+(1035360643/2500000000 : ℝ)*X 0 1+(1122863627/2500000000 : ℝ)*X 0 2+(2156602751/5000000000 : ℝ)*X 1 0+(1035360643/2500000000 : ℝ)*X 1 1+(1122863627/2500000000 : ℝ)*X 1 2+(2156602751/5000000000 : ℝ)*X 2 0+(1035360643/2500000000 : ℝ)*X 2 1+(1122863627/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-999950581/5000000000 : ℝ)*X 0 0+(5246688389/10000000000 : ℝ)*X 0 1+(8655039/16000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305573263/10000000000 : ℝ)*X 1 0+(-96002709/500000000 : ℝ)*X 1 1+(5409399483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4313230593/10000000000 : ℝ)*X 0 0+(89803927/200000000 : ℝ)*X 0 1+(4142706993/10000000000 : ℝ)*X 0 2+(4313230593/10000000000 : ℝ)*X 1 0+(89803927/200000000 : ℝ)*X 1 1+(4142706993/10000000000 : ℝ)*X 1 2+(4313230593/10000000000 : ℝ)*X 2 0+(89803927/200000000 : ℝ)*X 2 1+(4142706993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s7_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17975098496689313746508091/3100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (859334081/100000000000000 : ℝ)*(base19) + (963136587/100000000000000 : ℝ)*(base23) + (19336287/50000000000000 : ℝ)*(lower2) + (5699379/6250000000000 : ℝ)*(upper5) + (447934300951353/10000000000000 : ℝ)*(major0) + (447934300951353/10000000000000 : ℝ)*(major1) + (447934300951353/10000000000000 : ℝ)*(major2) + (3050792534274959/50000000000000 : ℝ)*(sp0) + (381350733065973/6250000000000 : ℝ)*(sp1) + (305080928781613/5000000000000 : ℝ)*(sp2) + (1428528018272609/50000000000000 : ℝ)*(sp3) + (34470218929/100000000000000 : ℝ)*(sp4) + (3475189599/50000000000000 : ℝ)*(sp5) + (10250432359/100000000000000 : ℝ)*(sp6) + (1428533143488789/50000000000000 : ℝ)*(f.failure) + (6101619538768847/100000000000000 : ℝ)*(f.sum) + (1192354749843/868000000000000000000000000 : ℝ)*base65 + (290315350028156121/43400000000000000000000000000000 : ℝ)*base67 + (180623105594443879/43400000000000000000000000000000 : ℝ)*base70 + (89964449261356121/43400000000000000000000000000000 : ℝ)*base71 + (759580289371/173600000000000000000000000 : ℝ)*base73 + (250863339315443879/43400000000000000000000000000000 : ℝ)*base76 + (184058701409756121/43400000000000000000000000000000 : ℝ)*base77 + (490554053939556121/43400000000000000000000000000000 : ℝ)*base79 + (3435748323187/868000000000000000000000000 : ℝ)*base81 + (30388323/5000000000000000000000 : ℝ)*base89 + (30388323/5000000000000000000000 : ℝ)*base91 + (30388323/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1394_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156781207/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1394_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1394_box_0 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1836645459/10000000000 : ℝ)*x 0 + (2693875469/5000000000 : ℝ)*x 1 + (538775101/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1836645459/10000000000 : ℝ)^2177 ≤ (10907057253087/100000000000000 : ℝ)^1665 := by
    have hnat : (1836645459 : ℕ)^2177*100000000000000^1665 ≤ 10907057253087^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836645459 10000000000 10907057253087 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693875469/5000000000 : ℝ)^2177 ≤ (44546470976333/100000000000000 : ℝ)^1665 := by
    have hnat : (2693875469 : ℕ)^2177*100000000000000^1665 ≤ 44546470976333^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693875469 5000000000 44546470976333 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538775101/1000000000 : ℝ)^2177 ≤ (5568308969337/12500000000000 : ℝ)^1665 := by
    have hnat : (538775101 : ℕ)^2177*12500000000000^1665 ≤ 5568308969337^1665*1000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538775101 1000000000 5568308969337 12500000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1836645459/10000000000 : ℝ), (2693875469/5000000000 : ℝ), (538775101/1000000000 : ℝ)] ![(10907057253087/100000000000000 : ℝ), (44546470976333/100000000000000 : ℝ), (5568308969337/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1836645459/10000000000 : ℝ)|^2177 ≤ (10907057253087/100000000000000 : ℝ)^1665
        have hw : |(-1836645459/10000000000 : ℝ)|=(1836645459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693875469/5000000000 : ℝ)|^2177 ≤ (44546470976333/100000000000000 : ℝ)^1665
        have hw : |(2693875469/5000000000 : ℝ)|=(2693875469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538775101/1000000000 : ℝ)|^2177 ≤ (5568308969337/12500000000000 : ℝ)^1665
        have hw : |(538775101/1000000000 : ℝ)|=(538775101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_box_1 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2642885451/5000000000 : ℝ)*x 0 + (-1976602263/10000000000 : ℝ)*x 1 + (215510043/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642885451/5000000000 : ℝ)^2177 ≤ (5430903466609/12500000000000 : ℝ)^1665 := by
    have hnat : (2642885451 : ℕ)^2177*12500000000000^1665 ≤ 5430903466609^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642885451 5000000000 5430903466609 12500000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1976602263/10000000000 : ℝ)^2177 ≤ (3001574949379/25000000000000 : ℝ)^1665 := by
    have hnat : (1976602263 : ℕ)^2177*25000000000000^1665 ≤ 3001574949379^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976602263 10000000000 3001574949379 25000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215510043/400000000 : ℝ)^2177 ≤ (22273236228693/50000000000000 : ℝ)^1665 := by
    have hnat : (215510043 : ℕ)^2177*50000000000000^1665 ≤ 22273236228693^1665*400000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215510043 400000000 22273236228693 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642885451/5000000000 : ℝ), (-1976602263/10000000000 : ℝ), (215510043/400000000 : ℝ)] ![(5430903466609/12500000000000 : ℝ), (3001574949379/25000000000000 : ℝ), (22273236228693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642885451/5000000000 : ℝ)|^2177 ≤ (5430903466609/12500000000000 : ℝ)^1665
        have hw : |(2642885451/5000000000 : ℝ)|=(2642885451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1976602263/10000000000 : ℝ)|^2177 ≤ (3001574949379/25000000000000 : ℝ)^1665
        have hw : |(-1976602263/10000000000 : ℝ)|=(1976602263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215510043/400000000 : ℝ)|^2177 ≤ (22273236228693/50000000000000 : ℝ)^1665
        have hw : |(215510043/400000000 : ℝ)|=(215510043/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_box_2 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5285771253/10000000000 : ℝ)*x 0 + (5387750759/10000000000 : ℝ)*x 1 + (-988301109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285771253/10000000000 : ℝ)^2177 ≤ (21723615752581/50000000000000 : ℝ)^1665 := by
    have hnat : (5285771253 : ℕ)^2177*50000000000000^1665 ≤ 21723615752581^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285771253 10000000000 21723615752581 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387750759/10000000000 : ℝ)^2177 ≤ (8909293808247/20000000000000 : ℝ)^1665 := by
    have hnat : (5387750759 : ℕ)^2177*20000000000000^1665 ≤ 8909293808247^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387750759 10000000000 8909293808247 20000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (988301109/5000000000 : ℝ)^2177 ≤ (12006299440123/100000000000000 : ℝ)^1665 := by
    have hnat : (988301109 : ℕ)^2177*100000000000000^1665 ≤ 12006299440123^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988301109 5000000000 12006299440123 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285771253/10000000000 : ℝ), (5387750759/10000000000 : ℝ), (-988301109/5000000000 : ℝ)] ![(21723615752581/50000000000000 : ℝ), (8909293808247/20000000000000 : ℝ), (12006299440123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285771253/10000000000 : ℝ)|^2177 ≤ (21723615752581/50000000000000 : ℝ)^1665
        have hw : |(5285771253/10000000000 : ℝ)|=(5285771253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387750759/10000000000 : ℝ)|^2177 ≤ (8909293808247/20000000000000 : ℝ)^1665
        have hw : |(5387750759/10000000000 : ℝ)|=(5387750759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-988301109/5000000000 : ℝ)|^2177 ≤ (12006299440123/100000000000000 : ℝ)^1665
        have hw : |(-988301109/5000000000 : ℝ)|=(988301109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_box_3 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1115057511/2500000000 : ℝ)*x 0 + (2121736001/5000000000 : ℝ)*x 1 + (1060867867/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1115057511/2500000000 : ℝ)^2177 ≤ (2174763326219/6250000000000 : ℝ)^1665 := by
    have hnat : (1115057511 : ℕ)^2177*6250000000000^1665 ≤ 2174763326219^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115057511 2500000000 2174763326219 6250000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121736001/5000000000 : ℝ)^2177 ≤ (815047401697/2500000000000 : ℝ)^1665 := by
    have hnat : (2121736001 : ℕ)^2177*2500000000000^1665 ≤ 815047401697^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121736001 5000000000 815047401697 2500000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060867867/2500000000 : ℝ)^2177 ≤ (6520378140731/20000000000000 : ℝ)^1665 := by
    have hnat : (1060867867 : ℕ)^2177*20000000000000^1665 ≤ 6520378140731^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060867867 2500000000 6520378140731 20000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1115057511/2500000000 : ℝ), (2121736001/5000000000 : ℝ), (1060867867/2500000000 : ℝ)] ![(2174763326219/6250000000000 : ℝ), (815047401697/2500000000000 : ℝ), (6520378140731/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1115057511/2500000000 : ℝ)|^2177 ≤ (2174763326219/6250000000000 : ℝ)^1665
        have hw : |(1115057511/2500000000 : ℝ)|=(1115057511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2121736001/5000000000 : ℝ)|^2177 ≤ (815047401697/2500000000000 : ℝ)^1665
        have hw : |(2121736001/5000000000 : ℝ)|=(2121736001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060867867/2500000000 : ℝ)|^2177 ≤ (6520378140731/20000000000000 : ℝ)^1665
        have hw : |(1060867867/2500000000 : ℝ)|=(1060867867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_box_4 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-270733737/1250000000 : ℝ)*x 0 + (1316489887/2500000000 : ℝ)*x 1 + (1053191843/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270733737/1250000000 : ℝ)^2177 ≤ (1691392273919/12500000000000 : ℝ)^1665 := by
    have hnat : (270733737 : ℕ)^2177*12500000000000^1665 ≤ 1691392273919^1665*1250000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270733737 1250000000 1691392273919 12500000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316489887/2500000000 : ℝ)^2177 ≤ (10808608170781/25000000000000 : ℝ)^1665 := by
    have hnat : (1316489887 : ℕ)^2177*25000000000000^1665 ≤ 10808608170781^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316489887 2500000000 10808608170781 25000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053191843/2000000000 : ℝ)^2177 ≤ (8646885821683/20000000000000 : ℝ)^1665 := by
    have hnat : (1053191843 : ℕ)^2177*20000000000000^1665 ≤ 8646885821683^1665*2000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053191843 2000000000 8646885821683 20000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-270733737/1250000000 : ℝ), (1316489887/2500000000 : ℝ), (1053191843/2000000000 : ℝ)] ![(1691392273919/12500000000000 : ℝ), (10808608170781/25000000000000 : ℝ), (8646885821683/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-270733737/1250000000 : ℝ)|^2177 ≤ (1691392273919/12500000000000 : ℝ)^1665
        have hw : |(-270733737/1250000000 : ℝ)|=(270733737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316489887/2500000000 : ℝ)|^2177 ≤ (10808608170781/25000000000000 : ℝ)^1665
        have hw : |(1316489887/2500000000 : ℝ)|=(1316489887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053191843/2000000000 : ℝ)|^2177 ≤ (8646885821683/20000000000000 : ℝ)^1665
        have hw : |(1053191843/2000000000 : ℝ)|=(1053191843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_box_5 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2685564109/5000000000 : ℝ)*x 0 + (-2025823323/10000000000 : ℝ)*x 1 + (263298011/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685564109/5000000000 : ℝ)^2177 ≤ (44366854629011/100000000000000 : ℝ)^1665 := by
    have hnat : (2685564109 : ℕ)^2177*100000000000000^1665 ≤ 44366854629011^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685564109 5000000000 44366854629011 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2025823323/10000000000 : ℝ)^2177 ≤ (12398705452473/100000000000000 : ℝ)^1665 := by
    have hnat : (2025823323 : ℕ)^2177*100000000000000^1665 ≤ 12398705452473^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025823323 10000000000 12398705452473 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263298011/500000000 : ℝ)^2177 ≤ (43234439896951/100000000000000 : ℝ)^1665 := by
    have hnat : (263298011 : ℕ)^2177*100000000000000^1665 ≤ 43234439896951^1665*500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263298011 500000000 43234439896951 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685564109/5000000000 : ℝ), (-2025823323/10000000000 : ℝ), (263298011/500000000 : ℝ)] ![(44366854629011/100000000000000 : ℝ), (12398705452473/100000000000000 : ℝ), (43234439896951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685564109/5000000000 : ℝ)|^2177 ≤ (44366854629011/100000000000000 : ℝ)^1665
        have hw : |(2685564109/5000000000 : ℝ)|=(2685564109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2025823323/10000000000 : ℝ)|^2177 ≤ (12398705452473/100000000000000 : ℝ)^1665
        have hw : |(-2025823323/10000000000 : ℝ)|=(2025823323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263298011/500000000 : ℝ)|^2177 ≤ (43234439896951/100000000000000 : ℝ)^1665
        have hw : |(263298011/500000000 : ℝ)|=(263298011/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_box_6 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (671391189/1250000000 : ℝ)*x 0 + (2632979441/5000000000 : ℝ)*x 1 + (-506455843/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671391189/1250000000 : ℝ)^2177 ≤ (44366868604647/100000000000000 : ℝ)^1665 := by
    have hnat : (671391189 : ℕ)^2177*100000000000000^1665 ≤ 44366868604647^1665*1250000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671391189 1250000000 44366868604647 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632979441/5000000000 : ℝ)^2177 ≤ (43234425533707/100000000000000 : ℝ)^1665 := by
    have hnat : (2632979441 : ℕ)^2177*100000000000000^1665 ≤ 43234425533707^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632979441 5000000000 43234425533707 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506455843/2500000000 : ℝ)^2177 ≤ (12398705844589/100000000000000 : ℝ)^1665 := by
    have hnat : (506455843 : ℕ)^2177*100000000000000^1665 ≤ 12398705844589^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506455843 2500000000 12398705844589 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671391189/1250000000 : ℝ), (2632979441/5000000000 : ℝ), (-506455843/2500000000 : ℝ)] ![(44366868604647/100000000000000 : ℝ), (43234425533707/100000000000000 : ℝ), (12398705844589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671391189/1250000000 : ℝ)|^2177 ≤ (44366868604647/100000000000000 : ℝ)^1665
        have hw : |(671391189/1250000000 : ℝ)|=(671391189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632979441/5000000000 : ℝ)|^2177 ≤ (43234425533707/100000000000000 : ℝ)^1665
        have hw : |(2632979441/5000000000 : ℝ)|=(2632979441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-506455843/2500000000 : ℝ)|^2177 ≤ (12398705844589/100000000000000 : ℝ)^1665
        have hw : |(-506455843/2500000000 : ℝ)|=(506455843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_box_7 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4165179979/10000000000 : ℝ)*x 0 + (1097736217/2500000000 : ℝ)*x 1 + (4390944793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4165179979/10000000000 : ℝ)^2177 ≤ (31817664748517/100000000000000 : ℝ)^1665 := by
    have hnat : (4165179979 : ℕ)^2177*100000000000000^1665 ≤ 31817664748517^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165179979 10000000000 31817664748517 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097736217/2500000000 : ℝ)^2177 ≤ (34091167997871/100000000000000 : ℝ)^1665 := by
    have hnat : (1097736217 : ℕ)^2177*100000000000000^1665 ≤ 34091167997871^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097736217 2500000000 34091167997871 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4390944793/10000000000 : ℝ)^2177 ≤ (1065348976141/3125000000000 : ℝ)^1665 := by
    have hnat : (4390944793 : ℕ)^2177*3125000000000^1665 ≤ 1065348976141^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4390944793 10000000000 1065348976141 3125000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4165179979/10000000000 : ℝ), (1097736217/2500000000 : ℝ), (4390944793/10000000000 : ℝ)] ![(31817664748517/100000000000000 : ℝ), (34091167997871/100000000000000 : ℝ), (1065348976141/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4165179979/10000000000 : ℝ)|^2177 ≤ (31817664748517/100000000000000 : ℝ)^1665
        have hw : |(4165179979/10000000000 : ℝ)|=(4165179979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097736217/2500000000 : ℝ)|^2177 ≤ (34091167997871/100000000000000 : ℝ)^1665
        have hw : |(1097736217/2500000000 : ℝ)|=(1097736217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4390944793/10000000000 : ℝ)|^2177 ≤ (1065348976141/3125000000000 : ℝ)^1665
        have hw : |(4390944793/10000000000 : ℝ)|=(4390944793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_box_8 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-41932103/200000000 : ℝ)*x 0 + (259093793/500000000 : ℝ)*x 1 + (5401745667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41932103/200000000 : ℝ)^2177 ≤ (3242036742971/25000000000000 : ℝ)^1665 := by
    have hnat : (41932103 : ℕ)^2177*25000000000000^1665 ≤ 3242036742971^1665*200000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41932103 200000000 3242036742971 25000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259093793/500000000 : ℝ)^2177 ≤ (42334030170641/100000000000000 : ℝ)^1665 := by
    have hnat : (259093793 : ℕ)^2177*100000000000000^1665 ≤ 42334030170641^1665*500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259093793 500000000 42334030170641 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401745667/10000000000 : ℝ)^2177 ≤ (8939564568911/20000000000000 : ℝ)^1665 := by
    have hnat : (5401745667 : ℕ)^2177*20000000000000^1665 ≤ 8939564568911^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401745667 10000000000 8939564568911 20000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41932103/200000000 : ℝ), (259093793/500000000 : ℝ), (5401745667/10000000000 : ℝ)] ![(3242036742971/25000000000000 : ℝ), (42334030170641/100000000000000 : ℝ), (8939564568911/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41932103/200000000 : ℝ)|^2177 ≤ (3242036742971/25000000000000 : ℝ)^1665
        have hw : |(-41932103/200000000 : ℝ)|=(41932103/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259093793/500000000 : ℝ)|^2177 ≤ (42334030170641/100000000000000 : ℝ)^1665
        have hw : |(259093793/500000000 : ℝ)|=(259093793/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401745667/10000000000 : ℝ)|^2177 ≤ (8939564568911/20000000000000 : ℝ)^1665
        have hw : |(5401745667/10000000000 : ℝ)|=(5401745667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_box_9 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5275958161/10000000000 : ℝ)*x 0 + (-246352211/1250000000 : ℝ)*x 1 + (540174571/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275958161/10000000000 : ℝ)^2177 ≤ (10835449431917/25000000000000 : ℝ)^1665 := by
    have hnat : (5275958161 : ℕ)^2177*25000000000000^1665 ≤ 10835449431917^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275958161 10000000000 10835449431917 25000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (246352211/1250000000 : ℝ)^2177 ≤ (747523684013/6250000000000 : ℝ)^1665 := by
    have hnat : (246352211 : ℕ)^2177*6250000000000^1665 ≤ 747523684013^1665*1250000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246352211 1250000000 747523684013 6250000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540174571/1000000000 : ℝ)^2177 ≤ (22348911654891/50000000000000 : ℝ)^1665 := by
    have hnat : (540174571 : ℕ)^2177*50000000000000^1665 ≤ 22348911654891^1665*1000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540174571 1000000000 22348911654891 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275958161/10000000000 : ℝ), (-246352211/1250000000 : ℝ), (540174571/1000000000 : ℝ)] ![(10835449431917/25000000000000 : ℝ), (747523684013/6250000000000 : ℝ), (22348911654891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275958161/10000000000 : ℝ)|^2177 ≤ (10835449431917/25000000000000 : ℝ)^1665
        have hw : |(5275958161/10000000000 : ℝ)|=(5275958161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-246352211/1250000000 : ℝ)|^2177 ≤ (747523684013/6250000000000 : ℝ)^1665
        have hw : |(-246352211/1250000000 : ℝ)|=(246352211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540174571/1000000000 : ℝ)|^2177 ≤ (22348911654891/50000000000000 : ℝ)^1665
        have hw : |(540174571/1000000000 : ℝ)|=(540174571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_box_10 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2637979081/5000000000 : ℝ)*x 0 + (5401745737/10000000000 : ℝ)*x 1 + (-1970817651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637979081/5000000000 : ℝ)^2177 ≤ (43341797738409/100000000000000 : ℝ)^1665 := by
    have hnat : (2637979081 : ℕ)^2177*100000000000000^1665 ≤ 43341797738409^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637979081 5000000000 43341797738409 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401745737/10000000000 : ℝ)^2177 ≤ (22348911800951/50000000000000 : ℝ)^1665 := by
    have hnat : (5401745737 : ℕ)^2177*50000000000000^1665 ≤ 22348911800951^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401745737 10000000000 22348911800951 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1970817651/10000000000 : ℝ)^2177 ≤ (1495047331327/12500000000000 : ℝ)^1665 := by
    have hnat : (1970817651 : ℕ)^2177*12500000000000^1665 ≤ 1495047331327^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970817651 10000000000 1495047331327 12500000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637979081/5000000000 : ℝ), (5401745737/10000000000 : ℝ), (-1970817651/10000000000 : ℝ)] ![(43341797738409/100000000000000 : ℝ), (22348911800951/50000000000000 : ℝ), (1495047331327/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637979081/5000000000 : ℝ)|^2177 ≤ (43341797738409/100000000000000 : ℝ)^1665
        have hw : |(2637979081/5000000000 : ℝ)|=(2637979081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401745737/10000000000 : ℝ)|^2177 ≤ (22348911800951/50000000000000 : ℝ)^1665
        have hw : |(5401745737/10000000000 : ℝ)|=(5401745737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1970817651/10000000000 : ℝ)|^2177 ≤ (1495047331327/12500000000000 : ℝ)^1665
        have hw : |(-1970817651/10000000000 : ℝ)|=(1970817651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_box_11 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4493575649/10000000000 : ℝ)*x 0 + (845302341/2000000000 : ℝ)*x 1 + (4226511667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4493575649/10000000000 : ℝ)^2177 ≤ (35136743386973/100000000000000 : ℝ)^1665 := by
    have hnat : (4493575649 : ℕ)^2177*100000000000000^1665 ≤ 35136743386973^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493575649 10000000000 35136743386973 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845302341/2000000000 : ℝ)^2177 ≤ (32431628493463/100000000000000 : ℝ)^1665 := by
    have hnat : (845302341 : ℕ)^2177*100000000000000^1665 ≤ 32431628493463^1665*2000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845302341 2000000000 32431628493463 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4226511667/10000000000 : ℝ)^2177 ≤ (32431628112209/100000000000000 : ℝ)^1665 := by
    have hnat : (4226511667 : ℕ)^2177*100000000000000^1665 ≤ 32431628112209^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226511667 10000000000 32431628112209 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4493575649/10000000000 : ℝ), (845302341/2000000000 : ℝ), (4226511667/10000000000 : ℝ)] ![(35136743386973/100000000000000 : ℝ), (32431628493463/100000000000000 : ℝ), (32431628112209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4493575649/10000000000 : ℝ)|^2177 ≤ (35136743386973/100000000000000 : ℝ)^1665
        have hw : |(4493575649/10000000000 : ℝ)|=(4493575649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845302341/2000000000 : ℝ)|^2177 ≤ (32431628493463/100000000000000 : ℝ)^1665
        have hw : |(845302341/2000000000 : ℝ)|=(845302341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4226511667/10000000000 : ℝ)|^2177 ≤ (32431628112209/100000000000000 : ℝ)^1665
        have hw : |(4226511667/10000000000 : ℝ)|=(4226511667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_box_12 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-953075527/5000000000 : ℝ)*x 0 + (2734870433/5000000000 : ℝ)*x 1 + (1313713127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (953075527/5000000000 : ℝ)^2177 ≤ (2862465703799/25000000000000 : ℝ)^1665 := by
    have hnat : (953075527 : ℕ)^2177*25000000000000^1665 ≤ 2862465703799^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953075527 5000000000 2862465703799 25000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734870433/5000000000 : ℝ)^2177 ≤ (45434898339667/100000000000000 : ℝ)^1665 := by
    have hnat : (2734870433 : ℕ)^2177*100000000000000^1665 ≤ 45434898339667^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734870433 5000000000 45434898339667 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313713127/2500000000 : ℝ)^2177 ≤ (43115238835279/100000000000000 : ℝ)^1665 := by
    have hnat : (1313713127 : ℕ)^2177*100000000000000^1665 ≤ 43115238835279^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313713127 2500000000 43115238835279 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-953075527/5000000000 : ℝ), (2734870433/5000000000 : ℝ), (1313713127/2500000000 : ℝ)] ![(2862465703799/25000000000000 : ℝ), (45434898339667/100000000000000 : ℝ), (43115238835279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-953075527/5000000000 : ℝ)|^2177 ≤ (2862465703799/25000000000000 : ℝ)^1665
        have hw : |(-953075527/5000000000 : ℝ)|=(953075527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734870433/5000000000 : ℝ)|^2177 ≤ (45434898339667/100000000000000 : ℝ)^1665
        have hw : |(2734870433/5000000000 : ℝ)|=(2734870433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313713127/2500000000 : ℝ)|^2177 ≤ (43115238835279/100000000000000 : ℝ)^1665
        have hw : |(1313713127/2500000000 : ℝ)|=(1313713127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_box_13 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5378911829/10000000000 : ℝ)*x 0 + (-2030210299/10000000000 : ℝ)*x 1 + (5254852397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378911829/10000000000 : ℝ)^2177 ≤ (4445093897657/10000000000000 : ℝ)^1665 := by
    have hnat : (5378911829 : ℕ)^2177*10000000000000^1665 ≤ 4445093897657^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378911829 10000000000 4445093897657 10000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2030210299/10000000000 : ℝ)^2177 ≤ (12433823368121/100000000000000 : ℝ)^1665 := by
    have hnat : (2030210299 : ℕ)^2177*100000000000000^1665 ≤ 12433823368121^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030210299 10000000000 12433823368121 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254852397/10000000000 : ℝ)^2177 ≤ (43115237644483/100000000000000 : ℝ)^1665 := by
    have hnat : (5254852397 : ℕ)^2177*100000000000000^1665 ≤ 43115237644483^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254852397 10000000000 43115237644483 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378911829/10000000000 : ℝ), (-2030210299/10000000000 : ℝ), (5254852397/10000000000 : ℝ)] ![(4445093897657/10000000000000 : ℝ), (12433823368121/100000000000000 : ℝ), (43115237644483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378911829/10000000000 : ℝ)|^2177 ≤ (4445093897657/10000000000000 : ℝ)^1665
        have hw : |(5378911829/10000000000 : ℝ)|=(5378911829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2030210299/10000000000 : ℝ)|^2177 ≤ (12433823368121/100000000000000 : ℝ)^1665
        have hw : |(-2030210299/10000000000 : ℝ)|=(2030210299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254852397/10000000000 : ℝ)|^2177 ≤ (43115237644483/100000000000000 : ℝ)^1665
        have hw : |(5254852397/10000000000 : ℝ)|=(5254852397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_box_14 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5378911783/10000000000 : ℝ)*x 0 + (2627426229/5000000000 : ℝ)*x 1 + (-50755257/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378911783/10000000000 : ℝ)^2177 ≤ (44450938479533/100000000000000 : ℝ)^1665 := by
    have hnat : (5378911783 : ℕ)^2177*100000000000000^1665 ≤ 44450938479533^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378911783 10000000000 44450938479533 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627426229/5000000000 : ℝ)^2177 ≤ (8623047659777/20000000000000 : ℝ)^1665 := by
    have hnat : (2627426229 : ℕ)^2177*20000000000000^1665 ≤ 8623047659777^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627426229 5000000000 8623047659777 20000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50755257/250000000 : ℝ)^2177 ≤ (497352928639/4000000000000 : ℝ)^1665 := by
    have hnat : (50755257 : ℕ)^2177*4000000000000^1665 ≤ 497352928639^1665*250000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50755257 250000000 497352928639 4000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378911783/10000000000 : ℝ), (2627426229/5000000000 : ℝ), (-50755257/250000000 : ℝ)] ![(44450938479533/100000000000000 : ℝ), (8623047659777/20000000000000 : ℝ), (497352928639/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378911783/10000000000 : ℝ)|^2177 ≤ (44450938479533/100000000000000 : ℝ)^1665
        have hw : |(5378911783/10000000000 : ℝ)|=(5378911783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627426229/5000000000 : ℝ)|^2177 ≤ (8623047659777/20000000000000 : ℝ)^1665
        have hw : |(2627426229/5000000000 : ℝ)|=(2627426229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50755257/250000000 : ℝ)|^2177 ≤ (497352928639/4000000000000 : ℝ)^1665
        have hw : |(-50755257/250000000 : ℝ)|=(50755257/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_box_15 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4137824257/10000000000 : ℝ)*x 0 + (2202191347/5000000000 : ℝ)*x 1 + (880876477/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4137824257/10000000000 : ℝ)^2177 ≤ (1577235600441/5000000000000 : ℝ)^1665 := by
    have hnat : (4137824257 : ℕ)^2177*5000000000000^1665 ≤ 1577235600441^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137824257 10000000000 1577235600441 5000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2202191347/5000000000 : ℝ)^2177 ≤ (17113822780917/50000000000000 : ℝ)^1665 := by
    have hnat : (2202191347 : ℕ)^2177*50000000000000^1665 ≤ 17113822780917^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202191347 5000000000 17113822780917 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880876477/2000000000 : ℝ)^2177 ≤ (34227642422087/100000000000000 : ℝ)^1665 := by
    have hnat : (880876477 : ℕ)^2177*100000000000000^1665 ≤ 34227642422087^1665*2000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880876477 2000000000 34227642422087 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4137824257/10000000000 : ℝ), (2202191347/5000000000 : ℝ), (880876477/2000000000 : ℝ)] ![(1577235600441/5000000000000 : ℝ), (17113822780917/50000000000000 : ℝ), (34227642422087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4137824257/10000000000 : ℝ)|^2177 ≤ (1577235600441/5000000000000 : ℝ)^1665
        have hw : |(4137824257/10000000000 : ℝ)|=(4137824257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2202191347/5000000000 : ℝ)|^2177 ≤ (17113822780917/50000000000000 : ℝ)^1665
        have hw : |(2202191347/5000000000 : ℝ)|=(2202191347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(880876477/2000000000 : ℝ)|^2177 ≤ (34227642422087/100000000000000 : ℝ)^1665
        have hw : |(880876477/2000000000 : ℝ)|=(880876477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1394_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156781207/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62879/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59043/100000 : ℝ) ∧ (80253/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84553/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7369/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11267/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7369/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11267/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7369/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11267/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7369/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11267/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7369/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11267/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7369/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11267/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11267/100000 : ℝ) ^ (4353/1024 : ℝ) ≤ (9316639312348741/100000000000000000000 : ℝ) := by
    have hpowers : (11267/100000 : ℝ)^4353 ≤ (9316639312348741/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11267 : ℕ)^4353*100000000000000000000^1024 ≤ 9316639312348741^1024*100000^4353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11267 100000 9316639312348741 100000000000000000000 4353 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11267/100000 : ℝ)) (X := (9316639312348741/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7369/50000 : ℝ) ^ (4353/1024 : ℝ) ≤ (29177748401669829/100000000000000000000 : ℝ) := by
    have hpowers : (7369/50000 : ℝ)^4353 ≤ (29177748401669829/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7369 : ℕ)^4353*100000000000000000000^1024 ≤ 29177748401669829^1024*50000^4353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7369 50000 29177748401669829 100000000000000000000 4353 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7369/50000 : ℝ)) (X := (29177748401669829/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009316639312348741/50000000000000000000 : ℝ) ≤ (1250054787267339/1250000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (50009316639312348741/50000000000000000000 : ℝ)^1024 ≤ (1250054787267339/1250000000000000 : ℝ)^4353 := by
      have hnat : (50009316639312348741 : ℕ)^1024*1250000000000000^4353 ≤ 1250054787267339^4353*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009316639312348741 50000000000000000000 1250054787267339 1250000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250054787267339/1250000000000000 : ℝ)) (X := (50009316639312348741/50000000000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003849438771401857/10000000000000000000 : ℝ) ≤ (5000452704481619/5000000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (10003849438771401857/10000000000000000000 : ℝ)^1024 ≤ (5000452704481619/5000000000000000 : ℝ)^4353 := by
      have hnat : (10003849438771401857 : ℕ)^1024*5000000000000000^4353 ≤ 5000452704481619^4353*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003849438771401857 10000000000000000000 5000452704481619 5000000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000452704481619/5000000000000000 : ℝ)) (X := (10003849438771401857/10000000000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029177748401669829/50000000000000000000 : ℝ) ≤ (2500343129946941/2500000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (50029177748401669829/50000000000000000000 : ℝ)^1024 ≤ (2500343129946941/2500000000000000 : ℝ)^4353 := by
      have hnat : (50029177748401669829 : ℕ)^1024*2500000000000000^4353 ≤ 2500343129946941^4353*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029177748401669829 50000000000000000000 2500343129946941 2500000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500343129946941/2500000000000000 : ℝ)) (X := (50029177748401669829/50000000000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9316639312348741/100000000000000000000 : ℝ) ≤ ((8675248864379900117/8677500000000000000 : ℝ)+2*(233555412263/173550000000000 : ℝ)*(11267/100000 : ℝ))^(4353/1024 : ℝ) := by
    rw [show (8675248864379900117/8677500000000000000 : ℝ)+2*(233555412263/173550000000000 : ℝ)*(11267/100000 : ℝ)=(1250054787267339/1250000000000000 : ℝ) by norm_num, show 1+2*(9316639312348741/100000000000000000000 : ℝ)=(50009316639312348741/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29177748401669829/100000000000000000000 : ℝ)+(9316639312348741/100000000000000000000 : ℝ) ≤ ((8675248864379900117/8677500000000000000 : ℝ)+(233555412263/173550000000000 : ℝ)*((7369/50000 : ℝ)+(11267/100000 : ℝ)))^(4353/1024 : ℝ) := by
    rw [show (8675248864379900117/8677500000000000000 : ℝ)+(233555412263/173550000000000 : ℝ)*((7369/50000 : ℝ)+(11267/100000 : ℝ))=(5000452704481619/5000000000000000 : ℝ) by norm_num, show 1+(29177748401669829/100000000000000000000 : ℝ)+(9316639312348741/100000000000000000000 : ℝ)=(10003849438771401857/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29177748401669829/100000000000000000000 : ℝ) ≤ ((8675248864379900117/8677500000000000000 : ℝ)+2*(233555412263/173550000000000 : ℝ)*(7369/50000 : ℝ))^(4353/1024 : ℝ) := by
    rw [show (8675248864379900117/8677500000000000000 : ℝ)+2*(233555412263/173550000000000 : ℝ)*(7369/50000 : ℝ)=(2500343129946941/2500000000000000 : ℝ) by norm_num, show 1+2*(29177748401669829/100000000000000000000 : ℝ)=(50029177748401669829/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8675248864379900117/8677500000000000000 : ℝ)*(X 1 0+X 2 0)+(233555412263/173550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (8675248864379900117/8677500000000000000 : ℝ)) (alpha := (233555412263/173550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8675248864379900117/8677500000000000000 : ℝ)*(X 0 1+X 2 1)+(233555412263/173550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (8675248864379900117/8677500000000000000 : ℝ)) (alpha := (233555412263/173550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8675248864379900117/8677500000000000000 : ℝ)*(X 0 2+X 1 2)+(233555412263/173550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (11267/100000 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (8675248864379900117/8677500000000000000 : ℝ)) (alpha := (233555412263/173550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1836645459/10000000000 : ℝ)*X 0 0+(2693875469/5000000000 : ℝ)*X 0 1+(538775101/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642885451/5000000000 : ℝ)*X 1 0+(-1976602263/10000000000 : ℝ)*X 1 1+(215510043/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285771253/10000000000 : ℝ)*X 2 0+(5387750759/10000000000 : ℝ)*X 2 1+(-988301109/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1115057511/2500000000 : ℝ)*X 0 0+(2121736001/5000000000 : ℝ)*X 0 1+(1060867867/2500000000 : ℝ)*X 0 2+(1115057511/2500000000 : ℝ)*X 1 0+(2121736001/5000000000 : ℝ)*X 1 1+(1060867867/2500000000 : ℝ)*X 1 2+(1115057511/2500000000 : ℝ)*X 2 0+(2121736001/5000000000 : ℝ)*X 2 1+(1060867867/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-270733737/1250000000 : ℝ)*X 0 0+(1316489887/2500000000 : ℝ)*X 0 1+(1053191843/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2685564109/5000000000 : ℝ)*X 1 0+(-2025823323/10000000000 : ℝ)*X 1 1+(263298011/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((671391189/1250000000 : ℝ)*X 2 0+(2632979441/5000000000 : ℝ)*X 2 1+(-506455843/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4165179979/10000000000 : ℝ)*X 0 0+(1097736217/2500000000 : ℝ)*X 0 1+(4390944793/10000000000 : ℝ)*X 0 2+(4165179979/10000000000 : ℝ)*X 1 0+(1097736217/2500000000 : ℝ)*X 1 1+(4390944793/10000000000 : ℝ)*X 1 2+(4165179979/10000000000 : ℝ)*X 2 0+(1097736217/2500000000 : ℝ)*X 2 1+(4390944793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-41932103/200000000 : ℝ)*X 0 0+(259093793/500000000 : ℝ)*X 0 1+(5401745667/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275958161/10000000000 : ℝ)*X 1 0+(-246352211/1250000000 : ℝ)*X 1 1+(540174571/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2637979081/5000000000 : ℝ)*X 2 0+(5401745737/10000000000 : ℝ)*X 2 1+(-1970817651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4493575649/10000000000 : ℝ)*X 0 0+(845302341/2000000000 : ℝ)*X 0 1+(4226511667/10000000000 : ℝ)*X 0 2+(4493575649/10000000000 : ℝ)*X 1 0+(845302341/2000000000 : ℝ)*X 1 1+(4226511667/10000000000 : ℝ)*X 1 2+(4493575649/10000000000 : ℝ)*X 2 0+(845302341/2000000000 : ℝ)*X 2 1+(4226511667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-953075527/5000000000 : ℝ)*X 0 0+(2734870433/5000000000 : ℝ)*X 0 1+(1313713127/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5378911829/10000000000 : ℝ)*X 1 0+(-2030210299/10000000000 : ℝ)*X 1 1+(5254852397/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5378911783/10000000000 : ℝ)*X 2 0+(2627426229/5000000000 : ℝ)*X 2 1+(-50755257/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4137824257/10000000000 : ℝ)*X 0 0+(2202191347/5000000000 : ℝ)*X 0 1+(880876477/2000000000 : ℝ)*X 0 2+(4137824257/10000000000 : ℝ)*X 1 0+(2202191347/5000000000 : ℝ)*X 1 1+(880876477/2000000000 : ℝ)*X 1 2+(4137824257/10000000000 : ℝ)*X 2 0+(2202191347/5000000000 : ℝ)*X 2 1+(880876477/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62879/100000 : ℝ) ≤ (-4546785869302508686116442398479/7231250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70536419/50000000000000 : ℝ)*(upper1) + (1032137/1000000000000 : ℝ)*(upper4) + (174891741/50000000000000 : ℝ)*(upper5) + (297840382624987/10000000000000 : ℝ)*(major0) + (297840382624987/10000000000000 : ℝ)*(major1) + (297840382624987/10000000000000 : ℝ)*(major2) + (16614497759/50000000000000 : ℝ)*(sp2) + (905166759/6250000000000 : ℝ)*(sp3) + (4078020926008813/100000000000000 : ℝ)*(sp4) + (254866608756829/6250000000000 : ℝ)*(sp5) + (203900673324229/5000000000000 : ℝ)*(sp6) + (949852720596783/50000000000000 : ℝ)*(sp7) + (12884735643/50000000000000 : ℝ)*(sp8) + (36191074167/20000000000000 : ℝ)*(sp13) + (189971992386171/10000000000000 : ℝ)*(f.failure) + (2039023347740049/50000000000000 : ℝ)*(f.sum) + (8379965750641/1735500000000000000000000000 : ℝ)*base65 + (65426812000324493/28925000000000000000000000000000 : ℝ)*base67 + (33088062471849493/28925000000000000000000000000000 : ℝ)*base69 + (203399751659099493/28925000000000000000000000000000 : ℝ)*base71 + (1979127677071/694200000000000000000000000 : ℝ)*base73 + (53141412548800507/28925000000000000000000000000000 : ℝ)*base76 + (264013528264624493/28925000000000000000000000000000 : ℝ)*base77 + (237730571491174493/28925000000000000000000000000000 : ℝ)*base79 + (6669661033421/1735500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (511603/1000000000000000000000 : ℝ)*base90 + (511603/1000000000000000000000 : ℝ)*base92 + (511603/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59043/100000 : ℝ) ≤ (3415795178468310148035117591/5785000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3017759/25000000000000 : ℝ)*(upper3) + (66808497/50000000000000 : ℝ)*(upper4) + (66545059/100000000000000 : ℝ)*(lower5) + (3048810030283837/100000000000000 : ℝ)*(major0) + (3048810030283837/100000000000000 : ℝ)*(major1) + (3048810030283837/100000000000000 : ℝ)*(major2) + (1033327665689031/25000000000000 : ℝ)*(sp0) + (64582964784959/1562500000000 : ℝ)*(sp1) + (16533238197183/400000000000 : ℝ)*(sp2) + (486156485089689/25000000000000 : ℝ)*(sp3) + (592041151/50000000000000 : ℝ)*(sp5) + (1281629551/100000000000000 : ℝ)*(sp7) + (53512711/20000000000000 : ℝ)*(sp8) + (172627991/12500000000000 : ℝ)*(sp10) + (1944627221988307/100000000000000 : ℝ)*(f.failure) + (2066655465159839/50000000000000 : ℝ)*(f.sum) + (68726325784823/17355000000000000000000000000 : ℝ)*base66 + (728234745593980357/289250000000000000000000000000000 : ℝ)*base68 + (1225060028365980357/289250000000000000000000000000000 : ℝ)*base70 + (34030490437230357/289250000000000000000000000000000 : ℝ)*base72 + (1316782672321/2169375000000000000000000000 : ℝ)*base74 + (1969950864945269643/289250000000000000000000000000000 : ℝ)*base75 + (1168745029216269643/289250000000000000000000000000000 : ℝ)*base77 + (622434739876519643/289250000000000000000000000000000 : ℝ)*base79 + (98392088023403/17355000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (11346549/10000000000000000000000 : ℝ)*base89 + (11346549/10000000000000000000000 : ℝ)*base91 + (11346549/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80253/100000 : ℝ) ≤ (163019463329779353838846235043/203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59609/2000000000000 : ℝ)*(lower2) + (1669449/12500000000000 : ℝ)*(upper4) + (168431/25000000000000 : ℝ)*(lower5) + (209908808773749/6250000000000 : ℝ)*(major0) + (209908808773749/6250000000000 : ℝ)*(major1) + (209908808773749/6250000000000 : ℝ)*(major2) + (591462347/4000000000000 : ℝ)*(sp1) + (15484874207/50000000000000 : ℝ)*(sp2) + (1548043331/25000000000000 : ℝ)*(sp3) + (83676881/100000000000000 : ℝ)*(sp4) + (1137036629307729/25000000000000 : ℝ)*(sp8) + (2274065907174561/50000000000000 : ℝ)*(sp9) + (4548115631159383/100000000000000 : ℝ)*(sp10) + (535544293936949/25000000000000 : ℝ)*(sp11) + (2142183367921121/100000000000000 : ℝ)*(f.failure) + (4548146600907797/100000000000000 : ℝ)*(f.sum) + (12912916246647/1446250000000000000000000000 : ℝ)*base65 + (108280996080451211/18078125000000000000000000000000 : ℝ)*base67 + (20680095359128667/2259765625000000000000000000000 : ℝ)*base69 + (397462281561201211/18078125000000000000000000000000 : ℝ)*base71 + (17185784564433/5785000000000000000000000000 : ℝ)*base73 + (91201346384124043/9039062500000000000000000000000 : ℝ)*base75 + (117693945444451211/18078125000000000000000000000000 : ℝ)*base77 + (81795971212155293/9039062500000000000000000000000 : ℝ)*base79 + (29287260544013/5785000000000000000000000000 : ℝ)*base81 + (31173047/10000000000000000000000 : ℝ)*base89 + (31173047/10000000000000000000000 : ℝ)*base91 + (31173047/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-84553/100000 : ℝ) ≤ (-61140240234296999487036464588001/72312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15625021/20000000000000 : ℝ)*(lower0) + (4797651/50000000000000 : ℝ)*(lower1) + (201987/2500000000000 : ℝ)*(lower2) + (2188843/20000000000000 : ℝ)*(lower4) + (1697805324897651/50000000000000 : ℝ)*(major0) + (1697805324897651/50000000000000 : ℝ)*(major1) + (1697805324897651/50000000000000 : ℝ)*(major2) + (912041457/100000000000000 : ℝ)*(sp0) + (66053358569/100000000000000 : ℝ)*(sp5) + (5279892781/12500000000000 : ℝ)*(sp6) + (4653576132714607/100000000000000 : ℝ)*(sp12) + (2326755495698747/50000000000000 : ℝ)*(sp13) + (930706961122763/20000000000000 : ℝ)*(sp14) + (433165519614261/20000000000000 : ℝ)*(sp15) + (433165519614261/20000000000000 : ℝ)*(f.failure) + (145424282648627/3125000000000 : ℝ)*(f.sum) + (4242919926907/723125000000000000000000000 : ℝ)*base66 + (1846275156652108389/144625000000000000000000000000000 : ℝ)*base67 + (1440369712849483389/144625000000000000000000000000000 : ℝ)*base69 + (3053685653160233389/144625000000000000000000000000000 : ℝ)*base71 + (30615216131661/5785000000000000000000000000 : ℝ)*base74 + (2175062923548983389/144625000000000000000000000000000 : ℝ)*base75 + (2691494243682608389/144625000000000000000000000000000 : ℝ)*base77 + (978686026221358389/144625000000000000000000000000000 : ℝ)*base79 + (20928949768381/5785000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (26006973/2000000000000000000000 : ℝ)*base90 + (26006973/2000000000000000000000 : ℝ)*base92 + (26006973/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1394_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156781207/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11267/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62879/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59043/100000 : ℝ) else (80253/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84553/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1394_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1394_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156781207/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62879/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59043/100000 : ℝ) else (80253/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84553/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1394_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1394_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1394_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156781207/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62879/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59043/100000 : ℝ) else (80253/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84553/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1394_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

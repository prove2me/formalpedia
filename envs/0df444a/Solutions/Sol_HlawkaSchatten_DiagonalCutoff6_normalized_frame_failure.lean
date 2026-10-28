-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff6.normalized_frame_failure
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T19:22:41.880394+00:00
-- url     : https://prove2.me/submissions/7330ae0d-6d40-4177-817c-f97ea819ddb7

import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_exists_normalized_failure
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_normalized_pair_sum_le
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_antitoneOn_scalarEnvelope
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
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
namespace HlawkaSchatten.DiagonalConstruction
variable {ι : Type*} [Fintype ι]
theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring
end HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalFailureBundle.Failure
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
section Deficit
variable {ι : Type*} [Fintype ι]

theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring

theorem hlawkaDeficit_swap_left (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K y x z = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

theorem hlawkaDeficit_swap_right (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x z y = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring

theorem scalarEnvelopeRoot_lt_one {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    scalarEnvelopeRoot p q < 1 := by
  have hpow : q ^ p < 1 := by
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow hq hq1 hp
  have hbase : 0 ≤ (1 + q ^ p) / 2 := by positivity
  have hroot := Real.rpow_lt_rpow hbase (show (1 + q ^ p) / 2 < 1 by linarith)
    (one_div_pos.mpr hp)
  simpa only [Real.one_rpow, scalarEnvelopeRoot] using hroot

theorem scalarEnvelope_denominator_pos {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 < 2 * (1 - scalarEnvelopeRoot p q) := by
  have h := scalarEnvelopeRoot_lt_one hp hq hq1
  linarith

theorem failure_ne_zero {p K : ℝ} (hp : 1 ≤ p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hf : hlawkaDeficit p K x y z < 0) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
  have hfirst (u v w : ι → ℝ) (h : hlawkaDeficit p K u v w < 0) : u ≠ 0 := by
    intro hu
    subst u
    simp only [hlawkaDeficit, lpNorm_zero (zero_lt_one.trans_le hp), zero_add] at h
    have ht := lpNorm_add hp v w
    have hm := mul_nonneg (sub_nonneg.mpr hK)
      (show 0 ≤ lpNorm p v + lpNorm p w - lpNorm p (v + w) by linarith)
    nlinarith
  refine ⟨hfirst x y z hf, hfirst y x z ?_, hfirst z x y ?_⟩
  · rwa [hlawkaDeficit_swap_left]
  · rwa [hlawkaDeficit_swap_left, hlawkaDeficit_swap_right]

theorem normalized_failure_total_lt_one {p K : ℝ} (hp : 1 ≤ p) (hK : 0 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) : lpNorm p (x + y + z) < 1 := by
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf
  have hprod := mul_nonneg hK (pairGapSum_nonneg hp x y z)
  linarith

theorem normalized_failure_ratio_lt_envelope {p K : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) :
    K < scalarEnvelope p (lpNorm p (x + y + z)) := by
  have hp0 := zero_lt_one.trans hp
  have hn := failure_ne_zero hp.le hK x y z hf
  have hq0 := lpNorm_nonneg p (x + y + z)
  have hq1 := normalized_failure_total_lt_one hp.le (by linarith) x y z hS hf
  have hP := normalized_pair_sum_le hp x y z hn.1 hn.2.1 hn.2.2 hS
  have hden := scalarEnvelope_denominator_pos hp0 hq0 hq1
  have hgap : 2 * (1 - scalarEnvelopeRoot p (lpNorm p (x + y + z))) ≤
      pairGapSum (lpNorm p) x y z := by
    dsimp only [pairGapSum, pairGap]
    linarith
  have hgap0 : 0 < pairGapSum (lpNorm p) x y z := hden.trans_le hgap
  have hR : K < (1 - lpNorm p (x + y + z)) / pairGapSum (lpNorm p) x y z := by
    rw [lt_div_iff₀ hgap0]
    rw [hlawkaDeficit_eq, tripleGap, hS] at hf
    linarith
  exact hR.trans_le (div_le_div_of_nonneg_left (by linarith) hden hgap)

/-- The envelope hypothesis at `q` confines the normalized total below `q`. -/
theorem normalized_failure_total_lt_q {p K q : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (hq0 : 0 < q) (hq1 : q < 1) (henvelope : scalarEnvelope p q < K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) :
    lpNorm p (x + y + z) < q := by
  have hT1 := normalized_failure_total_lt_one hp.le (by linarith) x y z hS hf
  have henv := normalized_failure_ratio_lt_envelope hp hK x y z hS hf
  by_contra hn
  have hle : q ≤ lpNorm p (x + y + z) := le_of_not_gt hn
  have hm := antitoneOn_scalarEnvelope hp.le
    (show q ∈ Set.Ico 0 1 from ⟨hq0.le, hq1⟩)
    (show lpNorm p (x + y + z) ∈ Set.Ico 0 1 from ⟨lpNorm_nonneg p _, hT1⟩) hle
  linarith

end Deficit

/-- Scaled normalization: singleton norms sum to 3, each at most the total,
and the total is below `3q`. -/
theorem scaled_failure {p K q : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (hq0 : 0 < q) (hq1 : q < 1) (henvelope : scalarEnvelope p q < K)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p K x y z < 0) :
    ∃ x y z : Fin 3 → ℝ, hlawkaDeficit p K x y z < 0 ∧
      lpNorm p x + lpNorm p y + lpNorm p z = 3 ∧
      lpNorm p x ≤ lpNorm p (x + y + z) ∧
      lpNorm p y ≤ lpNorm p (x + y + z) ∧
      lpNorm p z ≤ lpNorm p (x + y + z) ∧
      lpNorm p (x + y + z) < 3 * q := by
  have hp0 : 0 < p := by linarith
  obtain ⟨x, y, z, hf, hS, hxT, hyT, hzT⟩ := exists_normalized_failure hp0 hK x y z hf
  have hT := normalized_failure_total_lt_q hp hK hq0 hq1 henvelope x y z hS hf
  have h3 : |(3 : ℝ)| = 3 := abs_of_pos (by norm_num)
  have hsum : (3 : ℝ) • x + (3 : ℝ) • y + (3 : ℝ) • z = (3 : ℝ) • (x + y + z) := by
    rw [smul_add, smul_add]
  refine ⟨(3 : ℝ) • x, (3 : ℝ) • y, (3 : ℝ) • z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlawkaDeficit_smul hp0, h3]
    linarith
  · rw [lpNorm_smul hp0, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, lpNorm_smul hp0, h3]
    linarith
  · rw [hsum, lpNorm_smul hp0, h3]
    linarith


end HlawkaSchatten.DiagonalFailureBundle.Failure
namespace HlawkaSchatten.DiagonalFailureBundle
theorem orient_add (e : Equiv.Perm (Fin 3)) (s x y : Fin 3 → ℝ) :
    orient e s (x + y) = orient e s x + orient e s y := by
  ext i
  exact mul_add _ _ _
theorem lpNorm_orient (p : ℝ) (e : Equiv.Perm (Fin 3)) (s x : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) : lpNorm p (orient e s x) = lpNorm p x := by
  calc
    _ = lpNorm p (x ∘ e) := by simp [lpNorm, orient, hs, Real.norm_eq_abs]
    _ = _ := lpNorm_comp_equiv p x e
theorem hlawkaDeficit_orient (p K : ℝ) (e : Equiv.Perm (Fin 3)) (s x y z : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) :
    hlawkaDeficit p K (orient e s x) (orient e s y) (orient e s z) =
      hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← orient_add, lpNorm_orient p e s _ hs]
end HlawkaSchatten.DiagonalFailureBundle

set_option autoImplicit false

namespace HlawkaSchatten.DiagonalCutoff8

/- Two pairwise sums attain their largest absolute coordinate at the same
   coordinate. Keep both triangle bounds for the third pair. The two possible
   relative signs give the same upper bound for the sum of all pair norms. -/
theorem collision_pair_sum_bound
    {a b c Na Nb Nc P1 P2 P3 S T d s r : ℝ}
    (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hs : s = 1 ∨ s = -1) (hr : r = 1 ∨ r = -1)
    (hb : |b| ≤ Nb) (hc : |c| ≤ Nc)
    (hcol : |a+b+c| ≤ T) (ha : |a| ≤ Na)
    (h1 : d*P1 ≤ s*(a+b)) (h2 : d*P2 ≤ r*(a+c))
    (h3 : P3 ≤ Nb+Nc) (h3' : P3 ≤ T+Na)
    (hS : Na+Nb+Nc = S)
    (hmin : S-2*T ≤ Na) (hmax : Na ≤ T) :
    d*(P1+P2+P3) ≤ d*S+(2-d)*T := by
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  have ha' := abs_le.mp ha
  have hcol' := abs_le.mp hcol
  have h3d := mul_le_mul_of_nonneg_left h3 hd
  have h3d' := mul_le_mul_of_nonneg_left h3' hd
  have hmind := mul_le_mul_of_nonneg_left hmin (sub_nonneg.mpr hd1)
  have hmaxd := mul_le_mul_of_nonneg_left hmax (sub_nonneg.mpr hd1)
  have hSd := congrArg (fun x : ℝ => d*x) hS
  rcases hs with rfl | rfl <;> rcases hr with rfl | rfl <;> nlinarith

theorem collision_incompatible_with_failure
    {P T A d k : ℝ}
    (hd : 0 < d) (hk : 0 ≤ k)
    (hP : d*P ≤ 3*d+(2-d)*T)
    (hT : T ≤ A) (hslope : 0 ≤ k*(2-d)-d)
    (hmargin : (k*(2-d)-d)*A < 3*d*(k-1))
    (hfail : k*(6-P)+T < 3) : False := by
  have hPk := mul_le_mul_of_nonneg_left hP hk
  have hTA := mul_le_mul_of_nonneg_left hT hslope
  have hfaild := mul_lt_mul_of_pos_left hfail hd
  nlinarith

/- These rational constants leave a margin greater than two in the normalized
   deficit. The separate scalar bounds k ≤ K_p and T ≤ A are not asserted here. -/
theorem collision_parameters8 :
    3*(87/100 : ℝ)^8 < 1 ∧
    0 ≤ (159/50 : ℝ)*(2-87/100)-87/100 ∧
    ((159/50 : ℝ)*(2-87/100)-87/100)*(57/40) <
      3*(87/100)*(159/50-1) := by
  norm_num

end HlawkaSchatten.DiagonalCutoff8

namespace HlawkaSchatten.DiagonalCutoff8
theorem norm_le_three_root_max {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ)
    (i : Fin 3) (hi : ∀ j, |x j| ≤ |x i|) :
    lpNorm p x ≤ (3 : ℝ) ^ (1 / p) * |x i| := by
  have hsum : (∑ j, |x j| ^ p) ≤ 3 * |x i| ^ p := by
    calc
      _ ≤ ∑ _ : Fin 3, |x i| ^ p :=
        Finset.sum_le_sum fun j _ ↦ Real.rpow_le_rpow (abs_nonneg _) (hi j) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun j _ ↦ Real.rpow_nonneg (abs_nonneg (x j)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.rpow_mul (abs_nonneg (x i)), mul_one_div_cancel hp.ne', Real.rpow_one] at h
  simpa only [lpNorm, Real.norm_eq_abs] using h
end HlawkaSchatten.DiagonalCutoff8
/- Coordinate permutation and normalization follow the Apache-2.0 proofs of
Ezzeri Esa, bwdaugherty and Yuxuan Xu. Relative main-coordinate bounds and the
combined-pair-gap contradiction are the new cutoff-12 improvements. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalCutoff6
open HlawkaSchatten.DiagonalCutoff8
open HlawkaSchatten.DiagonalFailureBundle


theorem exists_relative_signed_coord {p d : ℝ} (hp : 0 < p) (hd : 0 ≤ d)
    (hdroot : d*(3 : ℝ)^(1/p) ≤ 1) (v : Fin 3 → ℝ) :
    ∃ i : Fin 3, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      d*lpNorm p v ≤ s*v i ∧ (∀ j, |v j| ≤ s*v i) := by
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image (fun i ↦ |v i|) Finset.univ_nonempty
  have h := norm_le_three_root_max hp v i (fun j => hi j (Finset.mem_univ _))
  have h1 := mul_le_mul_of_nonneg_left h hd
  have h2 := mul_le_mul_of_nonneg_right hdroot (abs_nonneg (v i))
  have h3 : d*lpNorm p v ≤ |v i| := by nlinarith
  by_cases hv : 0 ≤ v i
  · refine ⟨i,1,Or.inl rfl,?_,?_⟩
    · simpa [abs_of_nonneg hv] using h3
    · intro j; simpa [abs_of_nonneg hv] using hi j (Finset.mem_univ _)
  · refine ⟨i,-1,Or.inr rfl,?_,?_⟩
    · simpa [abs_of_neg (lt_of_not_ge hv)] using h3
    · intro j; simpa [abs_of_neg (lt_of_not_ge hv)] using hi j (Finset.mem_univ _)

theorem exists_relative_oriented_failure {p q k d : ℝ} (hp1 : 1 < p)
    (hq0 : 0 < q) (hqcap : q < 1) (hk : 1 ≤ k)
    (hd : 0 < d) (hd1 : d ≤ 1) (hdroot : d*(3 : ℝ)^(1/p) ≤ 1)
    (hslope : 0 ≤ k*(2-d)-d)
    (hmargin : (k*(2-d)-d)*(3*q) < 3*d*(k-1))
    (hlinear : k < cyclicConstant p)
    (henvelope : scalarEnvelope p q < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X : Fin 3 → Fin 3 → ℝ, RelativeOrientedData p q k d X := by
  set K := cyclicConstant p with hKdef
  have hK : k < K := by linarith
  obtain ⟨x, y, z, hf, hS, hxT, hyT, hzT, hTq⟩ :=
    Failure.scaled_failure hp1 (by linarith) hq0
      (by linarith) henvelope x y z hf
  set T := lpNorm p (x+y+z) with hTdef
  have hT : T < 3*q := by linarith
  have hG0 := pairGapSum_nonneg hp1.le x y z
  have hKG : K*pairGapSum (lpNorm p) x y z < 3-T := by
    have h := hf
    rw [hlawkaDeficit_eq, tripleGap, hS] at h
    linarith
  have hG : k*pairGapSum (lpNorm p) x y z+T < 3 := by
    have := mul_le_mul_of_nonneg_right hK.le hG0
    linarith
  have hTone : 1 ≤ T := by linarith
  have hTglobal : T ≤ 3*q := by linarith
  have hPfail : k*(6-(lpNorm p (x+y)+lpNorm p (x+z)+lpNorm p (y+z)))+T < 3 := by
    dsimp only [pairGapSum,pairGap] at hG
    have hSk := congrArg (fun r : ℝ => k*r) hS
    nlinarith only [hG,hSk]
  have hyzT : lpNorm p (y+z) ≤ T+lpNorm p x := by
    have h := lpNorm_add hp1.le (x+y+z) (-x)
    have he : (x+y+z)+(-x) = y+z := by abel
    rw [he,lpNorm_neg] at h
    exact h
  have hxzT : lpNorm p (x+z) ≤ T+lpNorm p y := by
    have h := lpNorm_add hp1.le (x+y+z) (-y)
    have he : (x+y+z)+(-y) = x+z := by abel
    rw [he,lpNorm_neg] at h
    exact h
  have hxyT : lpNorm p (x+y) ≤ T+lpNorm p z := by
    have h := lpNorm_add hp1.le (x+y+z) (-z)
    have he : (x+y+z)+(-z) = x+y := by abel
    rw [he,lpNorm_neg] at h
    exact h
  obtain ⟨i,s,hs,hsxy,hsxymax⟩ := exists_relative_signed_coord (by linarith : 0 < p) hd.le hdroot (x+y)
  obtain ⟨j,r,hr,hrxz,hrxzmax⟩ := exists_relative_signed_coord (by linarith : 0 < p) hd.le hdroot (x+z)
  obtain ⟨l,t,ht,htyz,htyzmax⟩ := exists_relative_signed_coord (by linarith : 0 < p) hd.le hdroot (y+z)
  simp only [Pi.add_apply, mul_add] at hsxy hrxz htyz
  have hxa (l : Fin 3) : |x l| ≤ lpNorm p x := norm_apply_le_lpNorm hp1.le x l
  have hya (l : Fin 3) : |y l| ≤ lpNorm p y := norm_apply_le_lpNorm hp1.le y l
  have hza (l : Fin 3) : |z l| ≤ lpNorm p z := norm_apply_le_lpNorm hp1.le z l
  have habs (l : Fin 3) : |x l+y l+z l| ≤ T := norm_apply_le_lpNorm hp1.le (x+y+z) l
  have hij : i ≠ j := by
    intro heq
    subst j
    have hb := collision_pair_sum_bound (d := d) (S := (3 : ℝ))
      (P1 := lpNorm p (x+y)) (P2 := lpNorm p (x+z))
      hd.le hd1 hs hr (hya i) (hza i) (habs i) (hxa i)
      (by nlinarith only [hsxy]) (by nlinarith only [hrxz])
      (lpNorm_add hp1.le y z) hyzT hS (by linarith) hxT
    exact collision_incompatible_with_failure (k := k)
      (d := d) (A := (3*q))
      (P := lpNorm p (x+y)+lpNorm p (x+z)+lpNorm p (y+z))
      hd (by linarith) (by nlinarith only [hb]) hTglobal
      hslope hmargin hPfail

  have hik : i ≠ l := by
    intro heq
    subst l
    have hcol : |y i+x i+z i| ≤ T := by
      rw [show y i+x i+z i = x i+y i+z i by ring]; exact habs i
    have hb := collision_pair_sum_bound (d := d) (S := (3 : ℝ))
      hd.le hd1 hs ht (hxa i) (hza i) hcol (hya i)
      (P1 := lpNorm p (x+y)) (P2 := lpNorm p (y+z))
      (by nlinarith only [hsxy]) (by nlinarith only [htyz])
      (lpNorm_add hp1.le x z) hxzT (by linarith) (by linarith) hyT
    exact collision_incompatible_with_failure (k := k)
      (d := d) (A := (3*q))
      (P := lpNorm p (x+y)+lpNorm p (x+z)+lpNorm p (y+z))
      hd (by linarith) (by nlinarith only [hb]) hTglobal
      hslope hmargin hPfail

  have hjk : j ≠ l := by
    intro heq
    subst l
    have hcol : |z j+x j+y j| ≤ T := by
      rw [show z j+x j+y j = x j+y j+z j by ring]; exact habs j
    have hb := collision_pair_sum_bound (d := d) (S := (3 : ℝ))
      hd.le hd1 hr ht (hxa j) (hya j) hcol (hza j)
      (P1 := lpNorm p (x+z)) (P2 := lpNorm p (y+z))
      (by nlinarith only [hrxz]) (by nlinarith only [htyz])
      (lpNorm_add hp1.le x y) hxyT (by linarith) (by linarith) hzT
    exact collision_incompatible_with_failure (k := k)
      (d := d) (A := (3*q))
      (P := lpNorm p (x+y)+lpNorm p (x+z)+lpNorm p (y+z))
      hd (by linarith) (by nlinarith only [hb]) hTglobal
      hslope hmargin hPfail

  let f : Fin 3 → Fin 3 := ![l, j, i]
  have hfInj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective f hfInj.bijective_of_finite
  let signs : Fin 3 → ℝ := ![t, r, s]
  have hsigns : ∀ l, |signs l| = 1 := by
    intro l
    fin_cases l
    · rcases ht with rfl | rfl <;> norm_num [signs]
    · rcases hr with rfl | rfl <;> norm_num [signs]
    · rcases hs with rfl | rfl <;> norm_num [signs]
  let u := orient e signs x
  let v := orient e signs y
  let w := orient e signs z
  have hu : lpNorm p u = lpNorm p x := lpNorm_orient p e signs x hsigns
  have hv : lpNorm p v = lpNorm p y := lpNorm_orient p e signs y hsigns
  have hw : lpNorm p w = lpNorm p z := lpNorm_orient p e signs z hsigns
  have hsumNorm : lpNorm p (u + v + w) = T := by
    dsimp [u, v, w]
    rw [← orient_add, ← orient_add, lpNorm_orient p e signs _ hsigns]
  have huv : lpNorm p (u + v) = lpNorm p (x + y) := by
    dsimp [u, v]; rw [← orient_add, lpNorm_orient p e signs _ hsigns]
  have huw : lpNorm p (u + w) = lpNorm p (x + z) := by
    dsimp [u, w]; rw [← orient_add, lpNorm_orient p e signs _ hsigns]
  have hvw : lpNorm p (v + w) = lpNorm p (y + z) := by
    dsimp [v, w]; rw [← orient_add, lpNorm_orient p e signs _ hsigns]
  have hpgs : pairGapSum (lpNorm p) u v w = pairGapSum (lpNorm p) x y z := by
    simp only [pairGapSum, pairGap, hu, hv, hw, huv, huw, hvw]
  have e0 : v 0 + w 0 = t * y l + t * z l := by simp [v, w, orient, e, f, signs]
  have e1 : u 1 + w 1 = r * x j + r * z j := by simp [u, w, orient, e, f, signs]
  have e2 : u 2 + v 2 = s * x i + s * y i := by simp [u, v, orient, e, f, signs]
  let X : Fin 3 → Fin 3 → ℝ := ![u, v, w]
  have hNX : ∀ l, lpNorm p (X l) ≤ T := by
    intro l
    fin_cases l
    · change lpNorm p u ≤ T
      rw [hu]; exact hxT
    · change lpNorm p v ≤ T
      rw [hv]; exact hyT
    · change lpNorm p w ≤ T
      rw [hw]; exact hzT
  have hlin : T - k * (lpNorm p (v + w) + lpNorm p (u + w) + lpNorm p (u + v)) ≤
      3 - 6 * k := by
    have hgf : pairGapSum (lpNorm p) u v w =
        6 - (lpNorm p (v + w) + lpNorm p (u + w) + lpNorm p (u + v)) := by
      dsimp only [pairGapSum, pairGap]
      rw [hu, hv, hw]
      linarith
    rw [← hpgs, hgf] at hG
    linarith
  refine ⟨![u, v, w], ?_⟩
  constructor
  · change lpNorm p u + lpNorm p v + lpNorm p w = 3
    rw [hu, hv, hw]; exact hS
  · intro l
    change lpNorm p (X l) ≤ lpNorm p (u + v + w)
    rw [hsumNorm]
    exact hNX l
  · change 1 ≤ lpNorm p (u + v + w)
    rw [hsumNorm]; exact hTone
  · change lpNorm p (u + v + w) < 3*q
    rw [hsumNorm]; exact hT
  · change d*lpNorm p (v+w) ≤ v 0+w 0
    rw [hvw, e0]; linarith
  · change d*lpNorm p (u+w) ≤ u 1+w 1
    rw [huw, e1]; linarith
  · change d*lpNorm p (u+v) ≤ u 2+v 2
    rw [huv, e2]; linarith
  · intro h
    change |(v+w) h| ≤ v 0+w 0
    rw [e0]
    have he : |(v+w) h| = |(y+z) (e h)| := by
      simp only [v,w,orient,Pi.add_apply,← mul_add,abs_mul,hsigns,one_mul]
    rw [he]
    simpa only [Pi.add_apply,mul_add] using htyzmax (e h)
  · intro h
    change |(u+w) h| ≤ u 1+w 1
    rw [e1]
    have he : |(u+w) h| = |(x+z) (e h)| := by
      simp only [u,w,orient,Pi.add_apply,← mul_add,abs_mul,hsigns,one_mul]
    rw [he]
    simpa only [Pi.add_apply,mul_add] using hrxzmax (e h)
  · intro h
    change |(u+v) h| ≤ u 2+v 2
    rw [e2]
    have he : |(u+v) h| = |(x+y) (e h)| := by
      simp only [u,v,orient,Pi.add_apply,← mul_add,abs_mul,hsigns,one_mul]
    rw [he]
    simpa only [Pi.add_apply,mul_add] using hsxymax (e h)
  · change lpNorm p (u+v+w) - k * (lpNorm p (v+w)+lpNorm p (u+w)+lpNorm p (u+v)) ≤ _
    rw [hsumNorm]; exact hlin
  · change hlawkaDeficit p K u v w < 0
    dsimp [u, v, w]
    rwa [hlawkaDeficit_orient p K e signs x y z hsigns]

end HlawkaSchatten.DiagonalCutoff6

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
end HlawkaSchatten.DiagonalCutoff6
set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff6
open HlawkaSchatten.DiagonalConstruction

theorem normalized_frame_failure {p q k d : ℝ} (hp : 1 < p)
    (hq0 : 0 < q) (hq1 : q < 1) (hk : 1 ≤ k)
    (hd : 0 < d) (hd1 : d ≤ 1) (hdroot : d*(3 : ℝ)^(1/p) ≤ 1)
    (hslope : 0 ≤ k*(2-d)-d)
    (hmargin : (k*(2-d)-d)*(3*q) < 3*d*(k-1))
    (hlinear : k < cyclicConstant p) (henvelope : scalarEnvelope p q < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X : Fin 3 → Fin 3 → ℝ, Frame p k (3*q) d X ∧ tripleDeficit p (cyclicConstant p) X < 0 := by
  obtain ⟨X,hX⟩ := exists_relative_oriented_failure hp hq0 hq1 hk hd hd1 hdroot hslope hmargin hlinear henvelope x y z hf
  exact ⟨X,oriented_frame hX,hX.failure⟩

end HlawkaSchatten.DiagonalCutoff6


open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem solution {p q k d : ℝ} (hp : 1 < p)
    (hq0 : 0 < q) (hq1 : q < 1) (hk : 1 ≤ k)
    (hd : 0 < d) (hd1 : d ≤ 1) (hdroot : d*(3 : ℝ)^(1/p) ≤ 1)
    (hslope : 0 ≤ k*(2-d)-d)
    (hmargin : (k*(2-d)-d)*(3*q) < 3*d*(k-1))
    (hlinear : k < cyclicConstant p) (henvelope : scalarEnvelope p q < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X : Fin 3 → Fin 3 → ℝ, Frame p k (3*q) d X ∧ tripleDeficit p (cyclicConstant p) X < 0 := by
  exact HlawkaSchatten.DiagonalCutoff6.normalized_frame_failure hp hq0 hq1 hk hd hd1 hdroot hslope hmargin hlinear henvelope x y z hf

#print axioms solution

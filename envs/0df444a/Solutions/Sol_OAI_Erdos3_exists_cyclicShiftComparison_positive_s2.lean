-- Prove2me | solution 1 for OAI.Erdos3.exists_cyclicShiftComparison_positive_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:59:18.625759+00:00
-- url     : https://prove2.me/submissions/32fbc66b-d8e4-487d-b434-a00bc7104efa

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B212
import Theorems.Thm_OAI_Erdos3_CellRefinement_exists_quantitative_bohr_bound_s2
import Theorems.Thm_OAI_Erdos3_PositiveShiftBasis_exists_bounded_native_contradiction_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem bilinear_shift_identity (a J : G → ℝ) (E : Finset G) (c : ℝ) :
    realBilinearAverage a (fun x => c * J x) (fun y => if -y ∈ E then 1 else 0) =
      c * (𝔼 h, if h ∈ E then realShiftCorrelation a J h else 0) := by
  have hy (x : G) :
      (𝔼 y, (c * J x) * (if -y ∈ E then 1 else 0) * a (x + y)) =
        c * (𝔼 h, if h ∈ E then J x * a (x - h) else 0) := by
    calc
      _ = 𝔼 h, (c * J x) * (if h ∈ E then 1 else 0) * a (x - h) := by
        apply Fintype.expect_equiv (Equiv.neg G)
        intro y
        simp
      _ = _ := by
        rw [Finset.mul_expect]
        apply Finset.expect_congr rfl
        intro h _
        by_cases hh : h ∈ E <;> simp [hh, mul_assoc]
  unfold realBilinearAverage
  simp_rw [hy]
  rw [← Finset.mul_expect, Finset.expect_comm]
  congr 1
  apply Finset.expect_congr rfl
  intro h _
  by_cases hh : h ∈ E
  · simp only [hh, ite_true, realShiftCorrelation]
    symm
    apply Fintype.expect_equiv (Equiv.addRight h)
    intro n
    simp [mul_comm]
  · simp [hh]

theorem bilinear_bound_bad_shift_density (a J : G → ℝ) {M δ ε : ℝ}
    (hM : 0 < M) (hδ : 0 < δ)
    (hJ : ∀ x, 0 ≤ J x ∧ J x ≤ M)
    (hbilinear : ∀ H W : G → ℝ, (∀ x, 0 ≤ H x ∧ H x ≤ 1) →
      (∀ x, 0 ≤ W x ∧ W x ≤ 1) → realBilinearAverage a H W ≤ ε) :
    let E := Finset.univ.filter (fun h => δ < realShiftCorrelation a J h)
    (E.card : ℝ) / Fintype.card G ≤ M * ε / δ := by
  classical
  intro E
  let H : G → ℝ := fun x => M⁻¹ * J x
  let W : G → ℝ := fun y => if -y ∈ E then 1 else 0
  have hH : ∀ x, 0 ≤ H x ∧ H x ≤ 1 := by
    intro x
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hM.le) (hJ x).1
    · dsimp [H]
      calc
        M⁻¹ * J x ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left (hJ x).2 (inv_nonneg.mpr hM.le)
        _ = 1 := inv_mul_cancel₀ hM.ne'
  have hW : ∀ x, 0 ≤ W x ∧ W x ≤ 1 := by
    intro x
    dsimp [W]
    split_ifs <;> norm_num
  have hb := hbilinear H W hH hW
  rw [bilinear_shift_identity] at hb
  have hsum : (E.card : ℝ) * δ ≤ ∑ h ∈ E, realShiftCorrelation a J h := by
    calc
      _ = ∑ _h ∈ E, δ := by simp
      _ ≤ _ := Finset.sum_le_sum (fun h hh => (Finset.mem_filter.mp hh).2.le)
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hlower : δ * ((E.card : ℝ) / Fintype.card G) ≤
      𝔼 h, if h ∈ E then realShiftCorrelation a J h else 0 := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [Finset.sum_ite_mem, Finset.univ_inter]
    have := div_le_div_of_nonneg_right hsum hcard.le
    simpa only [mul_div_assoc, mul_comm] using this
  have hupper : (𝔼 h, if h ∈ E then realShiftCorrelation a J h else 0) ≤ M * ε := by
    have h := mul_le_mul_of_nonneg_left hb hM.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul] using h
  exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hlower.trans hupper)

theorem exists_small_bad_shift_set (a J : G → ℝ) {p : ℝ} (hp : 0 ≤ p)
    (hJ : ∀ x, 0 ≤ J x ∧ J x ≤ Real.exp p)
    (hbilinear : ∀ H W : G → ℝ, (∀ x, 0 ≤ H x ∧ H x ≤ 1) →
      (∀ x, 0 ≤ W x ∧ W x ≤ 1) → realBilinearAverage a H W ≤ Real.exp (-4 * p)) :
    ∃ E : Finset G, (E.card : ℝ) ≤ Real.exp (-p) * Fintype.card G ∧
      ∀ h ∉ E, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        realShiftCorrelation a J h * t ≤ Real.exp (-p) := by
  classical
  let E := Finset.univ.filter (fun h => Real.exp (-p) < realShiftCorrelation a J h)
  have h := bilinear_bound_bad_shift_density a J (Real.exp_pos p) (Real.exp_pos (-p)) hJ hbilinear
  change (E.card : ℝ) / Fintype.card G ≤ _ at h
  have hexp : Real.exp p * Real.exp (-4 * p) / Real.exp (-p) ≤ Real.exp (-p) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    linarith
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  refine ⟨E, (div_le_iff₀ hcard).mp (h.trans hexp), ?_⟩
  intro k hk t ht ht1
  have hk' : realShiftCorrelation a J k ≤ Real.exp (-p) := by
    simpa only [E, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hk
  exact (mul_le_mul_of_nonneg_right hk' ht).trans
    (mul_le_of_le_one_right (Real.exp_nonneg _) ht1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FlatWeightedComparison
namespace OAI


namespace Erdos3.LocalConvolution

open scoped BigOperators

theorem momentAmplificationFactor_pos (delta : ℝ) : 0 < momentAmplificationFactor delta := by
  unfold momentAmplificationFactor
  omega

theorem momentAmplificationGain_pos (delta : ℝ) : 0 < momentAmplificationGain delta := by
  have hR : (0 : ℝ) < momentAmplificationFactor delta := by
    exact_mod_cast momentAmplificationFactor_pos delta
  have h := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity : 0 < 1 / (momentAmplificationFactor delta : ℝ))
  unfold momentAmplificationGain
  linarith

theorem momentAmplificationGain_le_one (delta : ℝ) : momentAmplificationGain delta ≤ 1 := by
  have hR : (1 : ℝ) ≤ momentAmplificationFactor delta := by
    exact_mod_cast momentAmplificationFactor_pos delta
  have hinv : 1 / (momentAmplificationFactor delta : ℝ) ≤ 1 :=
    (div_le_one (by linarith)).mpr hR
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hinv
  rw [Real.rpow_one] at h
  unfold momentAmplificationGain
  linarith

end Erdos3.LocalConvolution


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalMomentScale
namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

theorem localMomentGain_pos (delta : ℝ) : 0 < localMomentGain delta :=
  div_pos (momentAmplificationGain_pos _) (by norm_num)

theorem localMomentGain_le_half (delta : ℝ) : localMomentGain delta ≤ 1 / 2 :=
  div_le_div_of_nonneg_right (momentAmplificationGain_le_one _) (by norm_num)

end Erdos3.LocalConvolution

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentReturnScale
namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped NNReal

theorem localMomentErrorBudget_spec {delta : ℝ} (hdelta : 0 < delta) :
    0 ≤ localMomentErrorBudget delta ∧
      Real.exp (-localMomentErrorBudget delta) / 2 = min (delta / 2) (localMomentGain delta) / 3 := by
  have hc : 0 < min (delta / 2) (localMomentGain delta) :=
    lt_min (by positivity) (localMomentGain_pos delta)
  have hc1 : min (delta / 2) (localMomentGain delta) ≤ 1 / 2 :=
    (min_le_right _ _).trans (localMomentGain_le_half delta)
  unfold localMomentErrorBudget
  constructor
  · exact neg_nonneg.mpr (Real.log_nonpos (by positivity) (by linarith))
  · rw [neg_neg, Real.exp_log (by positivity)]
    ring

end Erdos3.LocalConvolution

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MatchedFlatDecay
namespace OAI

section

namespace Erdos3

theorem flatComparisonDelta_spec {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < flatComparisonDelta epsilon ∧ flatComparisonDelta epsilon ≤ 1 / 4 ∧
      1 + 2 * flatComparisonDelta epsilon ≤
        (1 + epsilon) * (1 - 2 * flatComparisonDelta epsilon) := by
  have hden : 0 < 4 * (2 + epsilon) := by positivity
  have hprod : flatComparisonDelta epsilon * (4 * (2 + epsilon)) = epsilon :=
    div_mul_cancel₀ _ hden.ne'
  refine ⟨div_pos hepsilon hden, ?_, ?_⟩
  · unfold flatComparisonDelta
    apply (div_le_iff₀ hden).mpr
    linarith
  · nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.UnbalancedWidthBudget
namespace OAI

section

namespace Erdos3.LocalConvolution

open CyclicCrootSisask

theorem unbalancedErrorBudget_spec {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    0 ≤ unbalancedErrorBudget c ∧ Real.exp (-unbalancedErrorBudget c) / 2 = c / 64 := by
  constructor
  · unfold unbalancedErrorBudget
    apply neg_nonneg.mpr
    exact Real.log_nonpos (by positivity) (by linarith)
  · unfold unbalancedErrorBudget
    rw [neg_neg, Real.exp_log (by positivity)]
    ring

end Erdos3.LocalConvolution

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.UnbalancedPolynomialBudget
namespace OAI

section

namespace Erdos3.LocalConvolution

open CyclicCrootSisask

theorem unbalancedRankExtra_le {c p H : ℝ} (hc : 0 < c) :
    (unbalancedRankExtra c p H : ℝ) ≤
      almostPeriodicityWidthConstant (c / 64) * (1 + (3 * H + 1) * p ^ 2) ^ 4 + 1 := by
  have hK := (almostPeriodicityWidthConstant_pos (show 0 < c / 64 by positivity)).le
  unfold unbalancedRankExtra
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem unbalancedWidthLoss_nonneg (rank : ℕ) {c p H : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hp : 0 ≤ p) (hH : 0 ≤ H) :
    0 ≤ unbalancedWidthLoss rank c p H := by
  have hK := (almostPeriodicityWidthConstant_pos (show 0 < c / 64 by positivity)).le
  have hE := (unbalancedErrorBudget_spec hc hc1).1
  have hlog : 0 ≤ Real.log (2 + (rank : ℝ)) :=
    Real.log_nonneg (by have hr : (0 : ℝ) ≤ (rank : ℝ) := Nat.cast_nonneg rank; linarith)
  unfold unbalancedWidthLoss
  positivity

theorem unbalancedWidthLoss_le_polynomial (rank : ℕ) {c p H : ℝ} (hc : 0 < c) :
    unbalancedWidthLoss rank c p H ≤
      2 * (rank : ℝ) +
        almostPeriodicityWidthConstant (c / 64) * (1 + (3 * H + 1) * p ^ 2) ^ 4 +
        2 * H * p ^ 2 + 2 * p + 2 * unbalancedErrorBudget c + 3209 +
        almostPeriodicityWidthConstant (c / 64) * (3 + (3 * H + 1) * p ^ 2 + rank) := by
  have hK := (almostPeriodicityWidthConstant_pos (show 0 < c / 64 by positivity)).le
  have hR := unbalancedRankExtra_le (p := p) (H := H) hc
  have hlog : Real.log (2 + (rank : ℝ)) ≤ (rank : ℝ) + 2 := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + (rank : ℝ))
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog hK
  unfold unbalancedWidthLoss
  push_cast
  nlinarith

end Erdos3.LocalConvolution

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget
namespace OAI

section

namespace Erdos3

theorem exists_natPolynomial_affine_budget (P : Polynomial ℕ) (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      P.eval₂ (Nat.castRingHom ℝ) ((A : ℝ) * (p + 1)) ≤ (p + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget
    (P.comp (Polynomial.C A * (Polynomial.X + 1)))
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [Polynomial.eval₂_comp] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem cyclicNiltestShiftBound_zero_of_constants.{u} {N : ℕ} [NeZero N]
    (a J : ZMod N → ℝ) (E : Finset (ZMod N)) {p error : ℝ}
    (hbound : ∀ h ∉ E, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → realShiftCorrelation a J h * t ≤ error) :
    CyclicNiltestShiftBound.{u} 0 N p error a J E := by
  intro h hh L _ _ s dim _ _ _ _ D hs T hT _
  have hs0 : s = 0 := by omega
  subst s
  let t := (T.observable (QuotientGroup.mk (1 : D.RealGroup))).re
  have ht : 0 ≤ t ∧ t ≤ 1 := (hT _).2
  have heval (x : ZMod N) : (T.evalCyclic N (fun _ => x)).re = t := by
    exact congrArg Complex.re (RationalFilteredNilmanifold.Niltest.eval_step_zero D T _)
  simp_rw [heval]
  rw [← Finset.expect_mul]
  exact hbound h hh t ht.1 ht.2

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem withUnitBound_eval (T : D.Niltest w) (hcap : ∀ x, ‖T.observable x‖ ≤ 1) (x : σ → ℤ) :
    (T.withUnitBound hcap).eval x = T.eval x := rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ExternalFamilyCircleProjection
namespace OAI

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

theorem iteratedCircleAverage_tested_error
    {X α G J : Type*} [PseudoMetricSpace X] [Fintype G] [Nonempty G] [Fintype J]
    (A : α → IsometricCircleAction X) (is : List α) (f : X → ℂ)
    (v : J → X → ℂ) (n : J → α → ℤ) (path : G → X) (weight : G → ℂ)
    (Lf : ℝ≥0) (Lv : J → ℝ≥0) (hf : LipschitzWith Lf f)
    (hv : ∀ j, LipschitzWith (Lv j) (v j))
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau)
    (hweight : ∀ x, ‖weight x‖ ≤ B)
    (happrox : ∀ x, ‖f x - ∑ j, v j x‖ ≤ rho)
    (heigen : ∀ j i, i ∈ is → ∀ t x, v j ((A i).act t x) = character (n j i • t) * v j x)
    (hdiscard : ∀ j, ¬ (∀ i ∈ is, n j i = 0) →
      ‖𝔼 x, weight x * v j (path x)‖ ≤ tau) :
    ‖(𝔼 x, weight x * f (path x)) -
      (𝔼 x, weight x * iteratedCircleAverage A is f (path x))‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  classical
  let keep : J → Prop := fun j => ∀ i ∈ is, n j i = 0
  have hsum (x : X) : iteratedCircleAverage A is (fun y => ∑ j, v j y) x =
      ∑ j, if keep j then v j x else 0 := by
    rw [iteratedCircleAverage_sum A is Finset.univ v Lv (fun j _ => hv j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [iteratedCircleAverage_eigenfunction A is (n j) (v j) (heigen j)]
    dsimp only [keep]
    split_ifs <;> rfl
  apply finite_projection_tested_error weight (fun x => f (path x))
    (fun x => iteratedCircleAverage A is f (path x))
    (fun j x => v j (path x)) keep hB htau hweight (fun x => happrox (path x)) _ hdiscard
  intro x
  rw [← hsum, norm_sub_rev]
  exact iteratedCircleAverage_sub_norm_le A is hf (lipschitz_finite_complex_sum v Lv hv)
    happrox (path x)

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalCentralCircle
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_centralRationalCircle_frequency (v : L) (hv : v ∈ D.filtration.layer s)
    (eta : L →ₗ[ℚ] ℚ) (f : D.Space → ℂ)
    (hf : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → ∀ x,
      f (z • x) = character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * f x) :
    let := D.metricSpace
    ∃ n : ℤ,
      (∀ t x, f ((D.centralRationalCircle v hv).act t x) = character (n • t) * f x) ∧
      (eta v = 0 → n = 0) := by
  classical
  let := D.metricSpace
  by_cases hz : ∀ x, f x = 0
  · exact ⟨0, fun t x => by simp [hz], fun _ => rfl⟩
  push Not at hz
  obtain ⟨n, hn⟩ := vertical_frequency_integral_on_lattice D.filtration D.realLattice eta f hf hz
    (⟨D.periodicRealDirection v⟩ : D.RealGroup)
    (D.periodicRealDirection_mem_top v hv) (D.periodicRealDirection_mem_lattice v)
  refine ⟨n, ?_, ?_⟩
  · intro t x
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    rw [D.centralRationalCircle_act_coe]
    have hr : realBCHLine (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.periodicRealDirection v) r ∈ D.filtration.realification.subgroup s := by
      change r • D.periodicRealDirection v ∈ D.filtration.realLayer s
      exact (D.filtration.realLayer s).smul_mem r (D.periodicRealDirection_mem_top v hv)
    rw [hf _ hr]
    apply congrArg (fun z : CircleFourier.Circle => character z * f x)
    change ((realifyFunctional eta (r • D.periodicRealDirection v) : ℝ) : CircleFourier.Circle) =
      n • (r : CircleFourier.Circle)
    rw [map_smul, hn, ← AddCircle.coe_zsmul]
    congr 1
    simp only [smul_eq_mul, zsmul_eq_mul, mul_comm]
  · intro heta
    have hzero : realifyFunctional eta (D.periodicRealDirection v) = 0 := by
      simp [periodicRealDirection, realifyFunctional_tmul, heta]
    have hn0 : (n : ℝ) = 0 := hn.symm.trans hzero
    exact_mod_cast hn0

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestProbabilityProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {σ α L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem averageCircles_orbit (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α) :
    (T.averageCircles A is).orbit = T.orbit := rfl

theorem averageCircles_complexity (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    {p : ℝ} (hT : T.ComplexityLE p) : (T.averageCircles A is).ComplexityLE p := hT

theorem averageCircles_tested_error (T : D.Niltest (fun _ : Unit => 1))
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    {J : Type*} [Fintype J] (U : J → D.Niltest (fun _ : Unit => 1)) (n : J → α → ℤ)
    (horbit : ∀ j, (U j).orbit = T.orbit) {N : ℕ} [NeZero N] (weight : ZMod N → ℂ)
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau) (hweight : ∀ x, ‖weight x‖ ≤ B)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (heigen : let := D.metricSpace; ∀ j i, i ∈ is → ∀ t x,
      (U j).observable ((A i).act t x) = character (n j i • t) * (U j).observable x)
    (hdiscard : ∀ j, ¬ (∀ i ∈ is, n j i = 0) →
      ‖𝔼 x, weight x * (U j).evalCyclic N (fun _ => x)‖ ≤ tau) :
    ‖(𝔼 x, weight x * T.evalCyclic N (fun _ => x)) -
      (𝔼 x, weight x * (T.averageCircles A is).evalCyclic N (fun _ => x))‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  let := D.metricSpace
  let path : ZMod N → D.Space := fun x => D.cyclicOrbitPoint T.orbit N (fun _ => x)
  have heval (j : J) (x : ZMod N) :
      (U j).observable (path x) = (U j).evalCyclic N (fun _ => x) := by
    change (U j).observable (D.cyclicOrbitPoint T.orbit N (fun _ => x)) =
      (U j).observable (D.cyclicOrbitPoint (U j).orbit N (fun _ => x))
    rw [horbit j]
  have hdiscard' (j : J) (hj : ¬ (∀ i ∈ is, n j i = 0)) :
      ‖𝔼 x, weight x * (U j).observable (path x)‖ ≤ tau := by
    simpa only [heval] using hdiscard j hj
  exact iteratedCircleAverage_tested_error A is T.observable (fun j => (U j).observable)
    n path weight T.lipBound (fun j => (U j).lipBound) T.lipschitz (fun j => (U j).lipschitz)
    hB htau hweight happrox heigen hdiscard'

theorem exists_positive_circle_projection (T : D.Niltest (fun _ : Unit => 1))
    (hT : T.UnitIntervalValued) {p : ℝ} (hTc : T.ComplexityLE p)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    (hcomm : let := D.metricSpace; ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j))
    {J : Type*} [Fintype J] (U : J → D.Niltest (fun _ : Unit => 1)) (n : J → α → ℤ)
    (horbit : ∀ j, (U j).orbit = T.orbit) {N : ℕ} [NeZero N] (weight : ZMod N → ℂ)
    {B rho tau : ℝ} (hB : 0 ≤ B) (htau : 0 ≤ tau) (hweight : ∀ x, ‖weight x‖ ≤ B)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (heigen : let := D.metricSpace; ∀ j i, i ∈ is → ∀ t x,
      (U j).observable ((A i).act t x) = character (n j i • t) * (U j).observable x)
    (hsignificant : ∀ j, tau < ‖𝔼 x, weight x * (U j).evalCyclic N (fun _ => x)‖ →
      ∀ i ∈ is, n j i = 0) :
    let := D.metricSpace
    ∃ S : D.Niltest (fun _ : Unit => 1), S.UnitIntervalValued ∧ S.ComplexityLE p ∧
      S.orbit = T.orbit ∧
      (∀ i ∈ is, ∀ t x, S.observable ((A i).act t x) = S.observable x) ∧
      ‖(𝔼 x, weight x * T.evalCyclic N (fun _ => x)) -
        (𝔼 x, weight x * S.evalCyclic N (fun _ => x))‖ ≤
        2 * B * rho + Fintype.card J * tau := by
  let := D.metricSpace
  refine ⟨T.averageCircles A is, T.averageCircles_unit_interval A is hT,
    T.averageCircles_complexity A is hTc, T.averageCircles_orbit A is, ?_, ?_⟩
  · intro i hi t x
    exact T.averageCircles_invariant A is hcomm i hi t x
  · apply T.averageCircles_tested_error A is U n horbit weight hB htau hweight happrox heigen
    intro j hj
    exact le_of_not_gt (fun h => hj (hsignificant j h))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefinementEnlargement
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution

theorem refinementContraction_bounds (epsilon : ℝ) :
    0 ≤ refinementContraction epsilon ∧ refinementContraction epsilon < 1 := by
  have hc := localMomentGain_pos (flatComparisonDelta epsilon)
  have hc1 := localMomentGain_le_half (flatComparisonDelta epsilon)
  unfold refinementContraction
  constructor <;> linarith

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

theorem refinement_enlargement_bounds {p : ℝ} (hp : 0 ≤ p) {A : ℕ} (hA : 512 ≤ A) :
    512 ≤ (A : ℝ) * (p + 1) ∧ p ≤ (A : ℝ) * (p + 1) ∧
      (A : ℝ) ≤ (A : ℝ) * (p + 1) := by
  have hAR : (512 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAR (by linarith : 0 ≤ p + 1)
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem refinement_enlargement_amplitude {p : ℝ} (hp : 0 ≤ p) {A : ℕ} (hA : 40 ≤ A) :
    2 * Real.exp p ≤ Real.exp (((A : ℝ) * (p + 1)) / 8) := by
  have hAR : (40 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAR (by linarith : 0 ≤ p + 1)
  calc
    _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (1 + p) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem refinement_enlargement_error {p : ℝ} (hp : 0 ≤ p) {A : ℕ} (hA : 40 ≤ A) :
    2 * Real.exp (-((A : ℝ) * (p + 1)) / 8) ≤ Real.exp (-4 * p) := by
  have hAR : (40 : ℝ) ≤ A := by exact_mod_cast hA
  have hm := mul_le_mul_of_nonneg_right hAR (by linarith : 0 ≤ p + 1)
  calc
    _ ≤ Real.exp 1 * Real.exp (-((A : ℝ) * (p + 1)) / 8) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (1 + -((A : ℝ) * (p + 1)) / 8) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem signed_comparison_amplitude {a b p epsilon : ℝ}
    (ha : 0 ≤ a ∧ a ≤ Real.exp p) (hb : 0 ≤ b ∧ b ≤ Real.exp p)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    |a - (1 + epsilon) * b| ≤ 2 * Real.exp p := by
  have hlo := mul_nonneg (show 0 ≤ 1 + epsilon by linarith) hb.1
  have hhi := mul_le_mul_of_nonneg_right (show 1 + epsilon ≤ 2 by linarith) hb.1
  exact abs_le.mpr ⟨by nlinarith, by nlinarith [Real.exp_pos p]⟩

end Erdos3.CellRefinement

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FixedRefinementBudget
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped NNReal

theorem refinementMatchingLoss_nonneg (rank : ℕ) {p epsilon : ℝ}
    (hp : 0 ≤ p) (hepsilon : 0 < epsilon) : 0 ≤ refinementMatchingLoss rank p epsilon := by
  have hdelta := (flatComparisonDelta_spec hepsilon).1
  have hc := localMomentGain_pos (flatComparisonDelta epsilon)
  have hc1 := (localMomentGain_le_half (flatComparisonDelta epsilon)).trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hEd := (localMomentErrorBudget_spec hdelta).1
  have hEc := (unbalancedErrorBudget_spec hc hc1).1
  unfold refinementMatchingLoss
  positivity

theorem two_le_refinementRoundLoss (rank : ℕ) {p H epsilon : ℝ}
    (hp : 0 ≤ p) (hH : 0 ≤ H) (hepsilon : 0 < epsilon) :
    2 ≤ refinementRoundLoss rank p H epsilon := by
  have hm := refinementMatchingLoss_nonneg rank hp hepsilon
  have hc := localMomentGain_pos (flatComparisonDelta epsilon)
  have hc1 := (localMomentGain_le_half (flatComparisonDelta epsilon)).trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hu := unbalancedWidthLoss_nonneg rank hc hc1 hp hH
  have hrank : (0 : ℝ) ≤ rank := Nat.cast_nonneg rank
  unfold refinementRoundLoss unbalancedReturnWidthLoss
  linarith

end Erdos3.CellRefinement

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

theorem mem_real_finiteFrequencyKernel (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ)
    (js : List J) (v : ℝ ⊗[ℚ] V) :
    v ∈ (finiteFrequencyKernel P eta js).baseChange ℝ ↔
      v ∈ P.baseChange ℝ ∧ ∀ j ∈ js, realifyFunctional (eta j) v = 0 := by
  induction js with
  | nil => simp [finiteFrequencyKernel]
  | cons j js ih =>
    simp only [finiteFrequencyKernel, realification_inf, Submodule.mem_inf,
      mem_realified_frequency_kernel_iff, ih, List.forall_mem_cons]
    tauto

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem exists_positive_frequency_projection_of_decomposition
    (T : D.Niltest (fun _ : Unit => 1)) (hT : T.UnitIntervalValued)
    {p : ℝ} (hTc : T.ComplexityLE p) {J : Type*} [Fintype J]
    (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest (fun _ : Unit => 1))
    (horbit : ∀ j, (U j).orbit = T.orbit)
    (hvertical : ∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    {N : ℕ} [NeZero N] (weight : ZMod N → ℂ) {B rho tau : ℝ}
    (hB : 0 ≤ B) (htau : 0 ≤ tau) (hweight : ∀ x, ‖weight x‖ ≤ B)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho) :
    ∃ S : D.Niltest (fun _ : Unit => 1), S.UnitIntervalValued ∧ S.ComplexityLE p ∧
      S.orbit = T.orbit ∧
      (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s →
        (∀ j, tau < ‖𝔼 n, weight n * (U j).evalCyclic N (fun _ => n)‖ →
          realifyFunctional (eta j) z.coord = 0) →
        ∀ x, S.observable (z • x) = S.observable x) ∧
      ‖(𝔼 n, weight n * T.evalCyclic N (fun _ => n)) -
        (𝔼 n, weight n * S.evalCyclic N (fun _ => n))‖ ≤
          2 * B * rho + Fintype.card J * tau := by
  classical
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let active : Finset J := Finset.univ.filter
    (fun j => tau < ‖𝔼 n, weight n * (U j).evalCyclic N (fun _ => n)‖)
  let js := active.toList
  let K := finiteFrequencyKernel (D.filtration.layer s) eta js
  have hK : K ≤ D.filtration.layer s := finiteFrequencyKernel_le _ _ _
  let b := Module.finBasis ℚ K
  let v : Fin (finrank ℚ K) → L := fun i => b i
  have hv (i : Fin (finrank ℚ K)) : v i ∈ D.filtration.layer s := hK (b i).property
  let A : Fin (finrank ℚ K) → IsometricCircleAction D.Space :=
    fun i => D.centralRationalCircle (v i) (hv i)
  have hfreq (j : J) (i : Fin (finrank ℚ K)) : ∃ n : ℤ,
      (∀ t x, (U j).observable ((A i).act t x) = character (n • t) * (U j).observable x) ∧
      (eta j (v i) = 0 → n = 0) :=
    D.exists_centralRationalCircle_frequency (v i) (hv i) (eta j) (U j).observable (hvertical j)
  choose n heigen hzero using hfreq
  let is := List.finRange (finrank ℚ K)
  have hcomm : ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j) :=
    fun i _ j _ => D.centralRationalCircle_commutes (v i) (v j) (hv i) (hv j)
  have hsignificant (j : J)
      (hj : tau < ‖𝔼 n, weight n * (U j).evalCyclic N (fun _ => n)‖) :
      ∀ i ∈ is, n j i = 0 := by
    intro i _
    apply hzero j i
    have hj' : j ∈ js := by simpa only [js, active, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and] using hj
    exact ((mem_finiteFrequencyKernel _ _ _ (v i)).mp (b i).property).2 j hj'
  obtain ⟨S, hS, hSc, hSo, hSinv, herror⟩ := T.exists_positive_circle_projection hT hTc A is hcomm
    U n horbit weight hB htau hweight happrox (fun j i _ => heigen j i) hsignificant
  refine ⟨S, hS, hSc, hSo, ?_, herror⟩
  intro z hz hzeta x
  have hzK : z.coord ∈ K.baseChange ℝ := by
    apply (mem_real_finiteFrequencyKernel (D.filtration.layer s) eta js z.coord).mpr
    refine ⟨hz, ?_⟩
    intro j hj
    apply hzeta j
    simpa only [js, active, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  exact D.invariant_of_kernel_circles K hK b S.observable
    (fun i t y => hSinv i (by simp [is]) t y) z hzK x

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PivotAnnihilatorFrequencyCode
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_restricted_frequency_basis_real_kernel
    {V J : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    ∃ m : ℕ, m ≤ finrank ℚ P ∧ ∃ indices : Fin m → J,
      (∀ i, indices i ∈ js) ∧
      LinearIndependent ℚ (fun i => (eta (indices i)).comp P.subtype) ∧
      ∀ x ∈ P.baseChange ℝ,
        (∀ j ∈ js, realifyFunctional (eta j) x = 0) ↔
          ∀ i, realifyFunctional (eta (indices i)) x = 0 := by
  obtain ⟨m, hm, indices, hmem, hlin, hspan⟩ := exists_restricted_frequency_basis P eta js
  have hK : finiteFrequencyKernel P eta js =
      finiteFrequencyKernel P (fun i => eta (indices i)) (List.finRange m) := by
    apply finiteFrequencyKernel_eq_of_span_eq
    rw [restrictedFrequencySpan_finRange]
    exact hspan.symm
  refine ⟨m, hm, indices, hmem, hlin, ?_⟩
  intro x hx
  constructor
  · intro h
    have hk := (mem_real_finiteFrequencyKernel P eta js x).mpr ⟨hx, h⟩
    rw [hK] at hk
    have hsel := (mem_real_finiteFrequencyKernel P (fun i => eta (indices i)) (List.finRange m) x).mp hk
    exact fun i => hsel.2 i (by simp)
  · intro h
    have hk := (mem_real_finiteFrequencyKernel P (fun i => eta (indices i)) (List.finRange m) x).mpr
      ⟨hx, fun i _ => h i⟩
    rw [← hK] at hk
    exact ((mem_real_finiteFrequencyKernel P eta js x).mp hk).2

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

theorem exists_bounded_positive_fourier_basis (T : D.Niltest (fun _ : Unit => 1))
    {p rho tau B : ℝ} (hp : 0 ≤ p) (hT : T.UnitIntervalValued) (hTc : T.ComplexityLE p)
    (hcap : T.normBound ≤ 1) (hrho : 0 < rho) (hrhop : rho⁻¹ ≤ Real.exp p)
    (htau : 0 ≤ tau) (hB : 0 ≤ B) {N : ℕ} [NeZero N]
    (weight : ZMod N → ℂ) (hweight : ∀ x, ‖weight x‖ ≤ B) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest (fun _ : Unit => 1))
      (S : D.Niltest (fun _ : Unit => 1)) (m : ℕ) (indices : Fin m → J),
      (Fintype.card J : ℝ) ≤ Real.exp (verticalDecompositionBudget p) ∧
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ j, (U j).ComplexityLE p ∧ (U j).orbit = T.orbit ∧ (U j).normBound ≤ 1) ∧
      (∀ j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        (U j).observable (z • x) =
          character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x) ∧
      m ≤ d ∧
      (∀ i, tau < ‖𝔼 n, weight n * (U (indices i)).evalCyclic N (fun _ => n)‖) ∧
      LinearIndependent ℚ (fun i => (eta (indices i)).comp (D.filtration.layer s).subtype) ∧
      S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
      (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s →
        (∀ i, realifyFunctional (eta (indices i)) z.coord = 0) →
        ∀ x, S.observable (z • x) = S.observable x) ∧
      ‖(𝔼 n, weight n * T.evalCyclic N (fun _ => n)) -
        (𝔼 n, weight n * S.evalCyclic N (fun _ => n))‖ ≤
          2 * B * rho + Real.exp (verticalDecompositionBudget p) * tau := by
  classical
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  obtain ⟨J, inst, eta, U, hcard, hheight, hU, hvertical, _, happrox, _⟩ :=
    T.exists_vertical_decomposition_preserving_bounds hp hTc hrho hrhop
  let := inst
  obtain ⟨S, hS, hSc, hSo, hinv, herr⟩ := T.exists_positive_frequency_projection_of_decomposition
    hT hTc eta U (fun j => (hU j).2.1) hvertical weight hB htau hweight
      (fun x => by simpa only [norm_sub_rev] using happrox x)
  let active : Finset J := Finset.univ.filter
    (fun j => tau < ‖𝔼 n, weight n * (U j).evalCyclic N (fun _ => n)‖)
  let js := active.toList
  obtain ⟨m, hm, indices, hindices, hlin, hkernel⟩ :=
    exists_restricted_frequency_basis_real_kernel (D.filtration.layer s) eta js
  have hmd : m ≤ d := hm.trans (by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using (D.filtration.layer s).finrank_le)
  refine ⟨J, inst, eta, U, S, m, indices, hcard, hheight, ?_, hvertical, hmd, ?_, hlin,
    hS, hSc, hSo, ?_, ?_⟩
  · intro j
    refine ⟨(hU j).1, (hU j).2.1, ?_⟩
    rw [(hU j).2.2.1]
    exact hcap
  · intro i
    simpa only [js, active, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
      using hindices i
  · intro z hz hbasis x
    apply hinv z hz _ x
    have hfull := (hkernel z.coord hz).mpr hbasis
    intro j hj
    exact hfull j (by simpa only [js, active, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and] using hj)
  · exact herr.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard htau))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonPositivePartitionRefinement
namespace OAI

section

universe u

namespace Erdos3

open scoped BigOperators

theorem real_shift_weighted_mean {N : ℕ} [NeZero N] (a J : ZMod N → ℝ)
    (T : ZMod N → ℂ) (h : ZMod N) :
    (𝔼 n, ((a n * J (n + h) : ℝ) : ℂ) * T n).re =
      𝔼 n, a n * J (n + h) * (T n).re := by
  simp only [expect_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem shift_violation_weight_cap {N : ℕ} {p epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (f g J : ZMod N → ℝ)
    (hf : ∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p)
    (hg : ∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p)
    (hJ : ∀ n, 0 ≤ J n ∧ J n ≤ Real.exp p) (h n : ZMod N) :
    ‖((((f n - (1 + epsilon) * g n) * J (n + h)) : ℝ) : ℂ)‖ ≤
      Real.exp (2 * p + 2) := by
  have ha : |f n - (1 + epsilon) * g n| ≤ 2 * Real.exp p := by
    apply abs_le.mpr
    have hprod : (1 + epsilon) * g n ≤ 2 * Real.exp p :=
      (mul_le_mul_of_nonneg_right (by linarith : 1 + epsilon ≤ 2) (hg n).1).trans
        (mul_le_mul_of_nonneg_left (hg n).2 (by norm_num))
    have hprod0 : 0 ≤ (1 + epsilon) * g n := mul_nonneg (by linarith) (hg n).1
    constructor <;> linarith [(hf n).1, (hf n).2, Real.exp_pos p]
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hJ _).1]
  calc
    _ ≤ (2 * Real.exp p) * Real.exp p := mul_le_mul ha (hJ _).2 (hJ _).1 (by positivity)
    _ ≤ (Real.exp 2 * Real.exp p) * Real.exp p := by gcongr
    _ = Real.exp (2 * p + 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem exists_many_positive_cyclic_violations {degree N : ℕ} [NeZero N]
    (a J : ZMod N → ℝ) {p error sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hfailure : ¬ ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ sigma * N ∧
      CyclicNiltestShiftBound.{u} degree N p error a J E) :
    ∃ (H : Finset (ZMod N)) (T : ZMod N → ZMod N → ℝ),
      H.Nonempty ∧ sigma * N < (H.card : ℝ) ∧
      (∀ h, PositiveCyclicNiltest.{u} degree N p (T h)) ∧
      ∀ h ∈ H, error < 𝔼 n, a n * J (n + h) * T h n := by
  classical
  let H : Finset (ZMod N) := Finset.univ.filter fun h =>
    ∃ T : ZMod N → ℝ, PositiveCyclicNiltest.{u} degree N p T ∧
      error < 𝔼 n, a n * J (n + h) * T n
  have hbound : CyclicNiltestShiftBound.{u} degree N p error a J H := by
    intro h hh L _ _ s d _ _ _ _ D hs T hT hTc
    by_contra hbad
    apply hh
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun n => (T.evalCyclic N (fun _ => n)).re,
      PositiveCyclicNiltest.of_test D hs T hT hTc (fun _ => rfl), lt_of_not_ge hbad⟩
  have hlarge : sigma * N < (H.card : ℝ) :=
    lt_of_not_ge (fun hsmall => hfailure ⟨H, hsmall, hbound⟩)
  have hH : H.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (lt_of_le_of_lt (mul_nonneg hsigma (Nat.cast_nonneg N)) hlarge)
  obtain ⟨h₀, hh₀⟩ := hH
  let pick (h : ZMod N) := if h ∈ H then h else h₀
  have hpick (h : ZMod N) : pick h ∈ H := by
    dsimp only [pick]
    split_ifs with hh
    · exact hh
    · exact hh₀
  have hchoices (h : ZMod N) : ∃ T : ZMod N → ℝ,
      PositiveCyclicNiltest.{u} degree N p T ∧
      error < 𝔼 n, a n * J (n + pick h) * T n := by
    simpa only [H, Finset.mem_filter, Finset.mem_univ, true_and] using hpick h
  choose T hT hcorr using hchoices
  refine ⟨H, T, ⟨h₀, hh₀⟩, hlarge, hT, ?_⟩
  intro h hh
  simpa only [pick, if_pos hh] using hcorr h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledAdaptedRebase
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

theorem exists_controlled_adapted_rebase :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      ∃ (F : D.AdaptedModelData) (H : ℕ)
        (hH : ∀ i j, RationalHeightLE (D.basis.repr (F.basis i) j) H),
        p ≤ (p + C) ^ C ∧ F.model.GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ {σ : Type*} {w : σ → ℕ} (T : D.Niltest w), T.ComplexityLE p →
          (F.rebaseNiltest H hH T).ComplexityLE ((p + C) ^ C)) ∧
        ∀ eta : L →ₗ[ℚ] ℚ, (∀ i, rationalLogHeight (eta (D.basis i)) ≤ p) →
          ∀ j, rationalLogHeight (eta (F.model.basis j)) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 3) ^ 11 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + 2) ^ 2 + (X + 3) ^ 4 + X)
  refine ⟨C, hC, ?_⟩
  intro L _ _ s d _ _ _ _ D p hp hD
  obtain ⟨F, hF, hb⟩ := D.exists_adapted_model_data hp hD
  let H := ⌈Real.exp (p + 1)⌉₊
  have hH (i j) : RationalHeightLE (D.basis.repr (F.basis i) j) H :=
    rationalHeightLE_ceil_exp (hb i j)
  let r := (p + 3) ^ 11 + p + 2
  have hpow : 0 ≤ (p + 3) ^ 11 := by positivity
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hfr : (p + 3) ^ 11 ≤ r := by dsimp [r]; linarith
  have hHbound : (H : ℝ) ≤ Real.exp r :=
    (ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)).trans
      (Real.exp_le_exp.mpr (by dsimp [r]; linarith))
  have hr : 0 ≤ r := hp.trans hpr
  have hbud : r + (r + 2) ^ 2 + (p + 3) ^ 4 + p ≤ (p + C) ^ C := by
    simpa [R, X, r, Polynomial.eval₂_pow] using hbudget p hp
  have hfreq0 : 0 ≤ (p + 3) ^ 4 := by positivity
  have hcomp : r + (r + 2) ^ 2 ≤ (p + C) ^ C := by linarith
  have hfreq : (p + 3) ^ 4 ≤ (p + C) ^ C := by nlinarith [sq_nonneg (r + 2)]
  have hbase : p ≤ (p + C) ^ C := hpr.trans ((le_add_of_nonneg_right (sq_nonneg _)).trans hcomp)
  have hgeom : F.model.GeometryComplexityLE r := hF.mono F.model hfr
  refine ⟨F, H, hH, hbase, hgeom.mono F.model
    ((le_add_of_nonneg_right (sq_nonneg _)).trans hcomp), ?_, ?_⟩
  · intro σ w T hT
    exact (F.rebaseNiltest_complexity H hH T hr (hT.mono hpr) hgeom hHbound).mono hcomp
  · intro eta heta j
    have hdim : (Fintype.card (Fin d) : ℝ) ≤ p + 1 := by
      simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith)
    have hval := rational_functional_value_logHeight D.basis eta
      (by linarith : 0 ≤ p + 1) hdim (fun i => (heta i).trans (by linarith : p ≤ p + 1))
      (F.basis j) (hb j)
    apply le_trans _ hfreq
    change rationalLogHeight (eta (F.basis j)) ≤ (p + 3) ^ 4
    simpa only [show p + 1 + 2 = p + 3 by ring] using hval

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ShiftFailurePositiveBasis
namespace OAI

section

namespace Erdos3

theorem positive_basis_error_bound (p v : ℝ) :
    2 * Real.exp p * Real.exp (-(2 * p + 8)) +
      Real.exp v * Real.exp (-(v + p + 8)) ≤ Real.exp (-p) / 2 := by
  have hfirst : Real.exp p * Real.exp (-(2 * p + 8)) = Real.exp (-p) * Real.exp (-8) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsecond : Real.exp v * Real.exp (-(v + p + 8)) = Real.exp (-p) * Real.exp (-8) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h6 : 6 * Real.exp (-8) ≤ 1 := by
    calc
      6 * Real.exp (-8) ≤ Real.exp 8 * Real.exp (-8) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (8 : ℝ)]) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; norm_num
  rw [mul_assoc (2 : ℝ), hfirst, hsecond]
  have hmul := mul_le_mul_of_nonneg_left h6 (Real.exp_pos (-p)).le
  nlinarith

theorem exists_positive_basis_precision :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → ∃ q rho tau : ℝ,
      p ≤ q ∧ q ≤ (p + C) ^ C ∧ verticalDecompositionBudget q ≤ (p + C) ^ C ∧
      0 < rho ∧ rho⁻¹ ≤ Real.exp q ∧ 0 < tau ∧ Real.exp (-((p + C) ^ C)) ≤ tau ∧
      2 * Real.exp p * rho + Real.exp (verticalDecompositionBudget q) * tau ≤ Real.exp (-p) / 2 := by
  obtain ⟨c, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let Q := 2 * X + 8
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C c) ^ c + X + 8)
  refine ⟨C, hC, ?_⟩
  intro p hp
  let q := 2 * p + 8
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq0 : 0 ≤ q := hp.trans hpq
  have hv0 := verticalDecompositionBudget_nonneg hq0
  have hb : q + (q + c) ^ c + p + 8 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hv := hvertical q hq0
  have hpow : 0 ≤ (q + c) ^ c := by positivity
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hvC : verticalDecompositionBudget q + p + 8 ≤ (p + C) ^ C := by linarith
  refine ⟨q, Real.exp (-q), Real.exp (-(verticalDecompositionBudget q + p + 8)),
    hpq, hqC, by linarith, Real.exp_pos _, ?_, Real.exp_pos _, ?_, ?_⟩
  · rw [Real.exp_neg, inv_inv]
  · exact Real.exp_le_exp.mpr (neg_le_neg hvC)
  · exact positive_basis_error_bound p (verticalDecompositionBudget q)

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_quantitative_positive_basis :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {D : RationalFilteredNilmanifold L s d} (T : D.Niltest (fun _ : Unit => 1))
      {p : ℝ}, 0 ≤ p → T.UnitIntervalValued → T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ {N : ℕ} [NeZero N] (weight : ZMod N → ℂ), (∀ x, ‖weight x‖ ≤ Real.exp p) →
      ∃ (m : ℕ) (eta : Fin m → L →ₗ[ℚ] ℚ) (U : Fin m → D.Niltest (fun _ : Unit => 1))
        (S : D.Niltest (fun _ : Unit => 1)),
        m ≤ d ∧
        (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ (p + C) ^ C) ∧
        (∀ j, (U j).ComplexityLE ((p + C) ^ C) ∧ (U j).orbit = T.orbit ∧ (U j).normBound ≤ 1) ∧
        (∀ j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          (U j).observable (z • x) =
            character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x) ∧
        (∀ j, Real.exp (-((p + C) ^ C)) < ‖𝔼 n, weight n * (U j).evalCyclic N (fun _ => n)‖) ∧
        LinearIndependent ℚ (fun j => (eta j).comp (D.filtration.layer s).subtype) ∧
        S.UnitIntervalValued ∧ S.ComplexityLE ((p + C) ^ C) ∧ S.orbit = T.orbit ∧
        (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s →
          (∀ j, realifyFunctional (eta j) z.coord = 0) → ∀ x, S.observable (z • x) = S.observable x) ∧
        ‖(𝔼 n, weight n * T.evalCyclic N (fun _ => n)) -
          (𝔼 n, weight n * S.evalCyclic N (fun _ => n))‖ ≤ Real.exp (-p) / 2 := by
  obtain ⟨C, hC, hprecision⟩ := exists_positive_basis_precision
  refine ⟨C, hC, ?_⟩
  intro L _ _ s d _ _ _ _ D T p hp hT hTc hcap N _ weight hweight
  obtain ⟨q, rho, tau, hpq, hqC, hvC, hrho, hrhoq, htau, htauC, hsmall⟩ := hprecision p hp
  obtain ⟨J, inst, hresult⟩ := T.exists_bounded_positive_fourier_basis (hp.trans hpq)
    hT (hTc.mono hpq) hcap hrho hrhoq htau.le (Real.exp_pos p).le weight hweight
  let := inst
  obtain ⟨eta, U, S, m, indices, _, hheight, hU, hvert, hmd, hcorr, hlin, hS, hSc, hSo, hinv, herr⟩ := hresult
  exact ⟨m, (fun j => eta (indices j)), (fun j => U (indices j)), S, hmd,
    (fun j i => (hheight (indices j) i).trans hvC),
    (fun j => ⟨(hU (indices j)).1.mono hqC, (hU (indices j)).2⟩),
    (fun j => hvert (indices j)), (fun j => htauC.trans_lt (hcorr j)), hlin,
    hS, hSc.mono hqC, hSo, hinv, herr.trans hsmall⟩

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

theorem positive_violation_of_norm_sub_le {a b : ℂ} {delta error : ℝ}
    (hviolation : delta < a.re) (herror : ‖a - b‖ ≤ error) (hsmall : error ≤ delta / 2) :
    delta / 2 < b.re := by
  have h := Complex.re_le_norm (a - b)
  rw [Complex.sub_re] at h
  linarith

namespace RationalFilteredNilmanifold

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_common_positive_basis :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (H : Finset G), H.Nonempty →
      ∀ (T : G → D.Niltest (fun _ : Unit => 1)) {p delta : ℝ}, 0 ≤ p →
      Real.exp (-p) ≤ delta →
      (∀ h ∈ H, (T h).UnitIntervalValued) →
      (∀ h ∈ H, (T h).ComplexityLE p) → (∀ h ∈ H, (T h).normBound ≤ 1) →
      ∀ {N : ℕ} [NeZero N] (weight : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ n, ‖weight h n‖ ≤ Real.exp p) →
      (∀ h ∈ H, delta < (𝔼 n, weight h n * (T h).evalCyclic N (fun _ => n)).re) →
      ∃ (m : ℕ) (H' : Finset G) (eta : G → Fin m → L →ₗ[ℚ] ℚ)
        (U : G → Fin m → D.Niltest (fun _ : Unit => 1)) (S : G → D.Niltest (fun _ : Unit => 1)),
        m ≤ d ∧ H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∀ h ∈ H',
          (∀ j i, rationalLogHeight (eta h j (D.basis i)) ≤ (p + C) ^ C) ∧
          (∀ j, (U h j).ComplexityLE ((p + C) ^ C) ∧ (U h j).orbit = (S h).orbit ∧ (U h j).normBound ≤ 1) ∧
          (∀ j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
            (U h j).observable (z • x) = character
              ((realifyFunctional (eta h j) z.coord : ℝ) : CircleFourier.Circle) * (U h j).observable x) ∧
          (∀ j, Real.exp (-((p + C) ^ C)) < ‖𝔼 n, weight h n * (U h j).evalCyclic N (fun _ => n)‖) ∧
          LinearIndependent ℚ (fun j => (eta h j).comp (D.filtration.layer s).subtype) ∧
          (S h).UnitIntervalValued ∧ (S h).ComplexityLE ((p + C) ^ C) ∧ (S h).orbit = (T h).orbit ∧
          (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s →
            (∀ j, realifyFunctional (eta h j) z.coord = 0) → ∀ x,
              (S h).observable (z • x) = (S h).observable x) ∧
          delta / 2 < (𝔼 n, weight h n * (S h).evalCyclic N (fun _ => n)).re := by
  classical
  obtain ⟨c, _, hbasis⟩ := Niltest.exists_quantitative_positive_basis
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C c) ^ c + 1)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ s d _ _ _ _ D H hH T p delta hp hdelta hT hTc hcap N _ weight hweight hviolation
  obtain ⟨hbase, hhbase⟩ := hH
  let pick (h : G) := if h ∈ H then h else hbase
  have hpick (h : G) : pick h ∈ H := by
    dsimp only [pick]
    split_ifs with hh
    · exact hh
    · exact hhbase
  have hchoices (h : G) := hbasis (T (pick h)) hp (hT _ (hpick h)) (hTc _ (hpick h))
    (hcap _ (hpick h)) (weight (pick h)) (hweight _ (hpick h))
  choose m eta U S hm hheight hU hvert hcorr hlin hS hSc hSo hinv herr using hchoices
  have hd : (d : ℝ) ≤ p := (hTc hbase hhbase).1.1
  have hpexp : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  obtain ⟨a, _, H', hsub, ha, hsame, hlarge⟩ :=
    exists_common_bounded_moduli H ⟨hbase, hhbase⟩ (fun h (_ : Unit) => m h) hp
      (fun h _ _ => ((Nat.cast_le.mpr (hm h)).trans hd).trans hpexp)
  let index (h : G) (hh : h ∈ H') : Fin (m a) ≃ Fin (m h) :=
    (finCongr (congrFun (hsame h hh) ())).symm
  let eta' (h : G) (j : Fin (m a)) : L →ₗ[ℚ] ℚ :=
    if hh : h ∈ H' then eta h (index h hh j) else 0
  let U' (h : G) (j : Fin (m a)) : D.Niltest (fun _ : Unit => 1) :=
    if hh : h ∈ H' then U h (index h hh j) else Niltest.const D (fun _ => 1) 0
  have hbud : p + (p + c) ^ c + 1 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcC : (p + c) ^ c ≤ (p + C) ^ C := by linarith
  have hpC : p + 1 ≤ (p + C) ^ C := by
    have hn : 0 ≤ (p + c) ^ c := by positivity
    linarith
  have hlarge' : Real.exp (-(p + 1)) * H.card ≤ (H'.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hlarge
  refine ⟨m a, H', eta', U', S, hm a, hsub, ⟨a, ha⟩,
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpC))
      (Nat.cast_nonneg _)).trans hlarge', ?_⟩
  intro h hh
  have hpickh : pick h = h := if_pos (hsub hh)
  simp only [eta', U', dif_pos hh]
  refine ⟨(fun j i => (hheight h (index h hh j) i).trans hcC), ?_,
    (fun j => hvert h (index h hh j)), ?_, ?_, hS h, (hSc h).mono hcC, ?_, ?_, ?_⟩
  · intro j
    exact ⟨(hU h (index h hh j)).1.mono hcC,
      (hU h (index h hh j)).2.1.trans (hSo h).symm, (hU h (index h hh j)).2.2⟩
  · intro j
    have ht := (Real.exp_le_exp.mpr (neg_le_neg hcC)).trans_lt (hcorr h (index h hh j))
    simpa only [hpickh] using ht
  · exact (hlin h).comp (index h hh) (index h hh).injective
  · simpa only [hpickh] using hSo h
  · intro z hz hzero x
    apply hinv h z hz _ x
    intro i
    obtain ⟨j, rfl⟩ := (index h hh).surjective i
    exact hzero j
  · have he : ‖(𝔼 n, weight h n * (T h).evalCyclic N (fun _ => n)) -
        (𝔼 n, weight h n * (S h).evalCyclic N (fun _ => n))‖ ≤ Real.exp (-p) / 2 := by
      simpa only [hpickh] using herr h
    exact positive_violation_of_norm_sub_le (hviolation h (hsub hh)) he (by linarith)

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_common_model_positive_basis (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)]
      [∀ h, TopologicalSpace (ℝ ⊗[ℚ] L h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] L h)]
      [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] L h)] [∀ h, T2Space (ℝ ⊗[ℚ] L h)] {d : G → ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s (d h))
      (T : ∀ h, (D h).Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p delta : ℝ}, 0 ≤ p → Real.exp (-p) ≤ delta → (∀ h, (T h).ComplexityLE p) →
      (∀ h ∈ H, (T h).UnitIntervalValued) →
      ∀ {N : ℕ} [NeZero N] (weight : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ n, ‖weight h n‖ ≤ Real.exp p) →
      (∀ h ∈ H, delta < (𝔼 n, weight h n * (T h).evalCyclic N (fun _ => n)).re) →
      ∃ h₀ ∈ H, ∃ E : RationalFilteredNilmanifold (L h₀) s (d h₀),
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ (m : ℕ) (H' : Finset G) (eta : G → Fin m → L h₀ →ₗ[ℚ] ℚ)
          (U : G → Fin m → E.Niltest (fun _ : Unit => 1)) (S : G → E.Niltest (fun _ : Unit => 1)),
          m ≤ d h₀ ∧ H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H',
            (∀ j i, rationalLogHeight (eta h j (E.basis i)) ≤ (p + C) ^ C) ∧
            (∀ j, (U h j).ComplexityLE ((p + C) ^ C) ∧ (U h j).orbit = (S h).orbit ∧ (U h j).normBound ≤ 1) ∧
            (∀ j z, z ∈ E.filtration.realification.subgroup s → ∀ x,
              (U h j).observable (z • x) = character
                ((realifyFunctional (eta h j) z.coord : ℝ) : CircleFourier.Circle) * (U h j).observable x) ∧
            (∀ j, Real.exp (-((p + C) ^ C)) < ‖𝔼 n, weight h n * (U h j).evalCyclic N (fun _ => n)‖) ∧
            LinearIndependent ℚ (fun j => (eta h j).comp (E.filtration.layer s).subtype) ∧
            (S h).UnitIntervalValued ∧ (S h).ComplexityLE ((p + C) ^ C) ∧
            (∀ z : E.RealGroup, z ∈ E.filtration.realification.subgroup s →
              (∀ j, realifyFunctional (eta h j) z.coord = 0) → ∀ x,
                (S h).observable (z • x) = (S h).observable x) ∧
            delta / 2 < (𝔼 n, weight h n * (S h).evalCyclic N (fun _ => n)).re := by
  classical
  obtain ⟨c, _, hmodels⟩ := exists_common_variable_dimension_niltest_model s
  obtain ⟨k, _, hbases⟩ := exists_common_positive_basis
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 1 + (X + 1 + Polynomial.C c) ^ c + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C k) ^ k)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p delta hp hdelta hTc hT N _ weight hweight hviolation
  let T₀ : ∀ h, (D h).Niltest (fun _ : Unit => 1) := fun h =>
    if hh : h ∈ H then (T h).withUnitBound (hT h hh).norm_le_one else T h
  have hTc₀ (h) : (T₀ h).ComplexityLE (p + 1) := by
    by_cases hh : h ∈ H
    · simpa only [T₀, dif_pos hh] using
        (T h).withUnitBound_complexity (hT h hh).norm_le_one (hTc h)
    · simpa only [T₀, dif_neg hh] using (hTc h).mono (by linarith : p ≤ p + 1)
  have hT₀ (h) (hh : h ∈ H) : (T₀ h).UnitIntervalValued := by
    simp only [T₀, dif_pos hh]
    exact hT h hh
  have hcap₀ (h) (hh : h ∈ H) : (T₀ h).normBound ≤ 1 := by
    simp only [T₀, dif_pos hh]
    exact le_rfl
  have hvalue₀ (h) (hh : h ∈ H) (x : Unit → ℤ) : (T₀ h).eval x = (T h).eval x := by
    simp only [T₀, dif_pos hh, Niltest.withUnitBound_eval]
  let q := p + 1 + (p + 1 + c) ^ c + 2
  have hpow : 0 ≤ (p + 1 + c) ^ c := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hmodelq : (p + 1 + c) ^ c ≤ q := by dsimp [q]; linarith
  have hq0 : 0 ≤ q := hp.trans hpq
  have hbud : q + (q + k) ^ k ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by
    have hh : 0 ≤ (q + k) ^ k := by positivity
    linarith
  have hbaseC : (q + k) ^ k ≤ (p + C) ^ C := by linarith
  have hloss : (p + 1 + c) ^ c + (q + k) ^ k ≤ (p + C) ^ C := by linarith
  obtain ⟨h₀, hh₀, E, hE, H₁, P, hsub₁, hh₀', hlarge₁, hP⟩ :=
    hmodels D T₀ H hH (by linarith : 0 ≤ p + 1) hTc₀
  have hPc (h) (hh : h ∈ H₁) : (P h).ComplexityLE q := (hP h hh).1.mono hmodelq
  have hPunit (h) (hh : h ∈ H₁) : (P h).UnitIntervalValued := (hP h hh).2.2.2 (hT₀ h (hsub₁ hh))
  have hPcap (h) (hh : h ∈ H₁) : (P h).normBound ≤ 1 := by
    rw [(hP h hh).2.1]
    exact hcap₀ h (hsub₁ hh)
  have hPvalue (h) (hh : h ∈ H₁) (n : ZMod N) :
      (P h).evalCyclic N (fun _ => n) = (T h).evalCyclic N (fun _ => n) :=
    ((hP h hh).2.2.1 _).trans (hvalue₀ h (hsub₁ hh) _)
  have hPviolation (h) (hh : h ∈ H₁) :
      delta < (𝔼 n, weight h n * (P h).evalCyclic N (fun _ => n)).re := by
    simpa only [hPvalue h hh] using hviolation h (hsub₁ hh)
  obtain ⟨m, H₂, eta, U, S, hm, hsub₂, hnonempty, hlarge₂, hbasis⟩ :=
    hbases E H₁ ⟨h₀, hh₀'⟩ P hq0
      ((Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hdelta) hPunit hPc hPcap weight
      (fun h hh n => (hweight h (hsub₁ hh) n).trans (Real.exp_le_exp.mpr hpq)) hPviolation
  refine ⟨h₀, hh₀, E, hE.mono E (hmodelq.trans hqC), m, H₂, eta, U, S, hm,
    hsub₂.trans hsub₁, hnonempty, ?_, ?_⟩
  · calc
      Real.exp (-((p + C) ^ C)) * H.card ≤
          Real.exp (-((p + 1 + c) ^ c + (q + k) ^ k)) * H.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hloss)) (Nat.cast_nonneg _)
      _ = Real.exp (-((q + k) ^ k)) * (Real.exp (-((p + 1 + c) ^ c)) * H.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((q + k) ^ k)) * H₁.card :=
        mul_le_mul_of_nonneg_left hlarge₁ (Real.exp_pos _).le
      _ ≤ H₂.card := hlarge₂
  · intro h hh
    obtain ⟨hheight, hU, hvert, hcorr, hlin, hS, hSc, _, hinv, hv⟩ := hbasis h hh
    exact ⟨(fun j i => (hheight j i).trans hbaseC),
      (fun j => ⟨(hU j).1.mono hbaseC, (hU j).2⟩), hvert,
      (fun j => (Real.exp_le_exp.mpr (neg_le_neg hbaseC)).trans_lt (hcorr j)),
      hlin, hS, hSc.mono hbaseC, hinv, hv⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_adapted :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s N : ℕ} [NeZero N] {p : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{u} s N p a J),
      ∃ (B' : PositiveShiftBasis.{u} s N ((p + C) ^ C) a J) (hcount : B'.count = B.count),
        (∃ weight : Fin B'.dim → ℕ, ∀ i, B'.model.filtration.layer i =
          Submodule.span ℚ (B'.model.basis '' {j | i ≤ weight j})) ∧
        B'.shifts = B.shifts ∧
        (∀ h j x, (B'.mode h j).eval x = (B.mode h (Fin.cast hcount j)).eval x) ∧
        ∀ h x, (B'.test h).eval x = (B.test h).eval x := by
  obtain ⟨C, hC, hrebase⟩ := RationalFilteredNilmanifold.exists_controlled_adapted_rebase
  refine ⟨C, hC, ?_⟩
  intro s N _ p a J B
  have hp : 0 ≤ p := (Nat.cast_nonneg B.dim).trans B.geometry.1
  obtain ⟨F, H, hH, hbase, hF, hcomp, hfreq⟩ := hrebase B.model hp B.geometry
  have hdim : finrank ℚ B.L = B.dim := by
    simpa only [Fintype.card_fin] using finrank_eq_card_basis B.model.basis
  let B' : PositiveShiftBasis s N ((p + C) ^ C) a J := {
    L := B.L
    lie := B.lie
    algebra := B.algebra
    dim := finrank ℚ B.L
    topology := B.topology
    topologicalAdd := B.topologicalAdd
    continuousSMul := B.continuousSMul
    hausdorff := B.hausdorff
    model := F.model
    geometry := hF
    count := B.count
    count_le_dim := by rw [hdim]; exact B.count_le_dim
    shifts := B.shifts
    shifts_nonempty := B.shifts_nonempty
    shifts_large := (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg hbase)) (Nat.cast_nonneg N)).trans B.shifts_large
    frequency := B.frequency
    mode := fun h j => F.rebaseNiltest H hH (B.mode h j)
    test := fun h => F.rebaseNiltest H hH (B.test h)
    frequency_height := fun h hh j => hfreq (B.frequency h j) (B.frequency_height h hh j)
    mode_complexity := fun h hh j => hcomp (B.mode h j) (B.mode_complexity h hh j)
    mode_orbit := fun h hh j => B.mode_orbit h hh j
    mode_norm := fun h hh j => B.mode_norm h hh j
    mode_vertical := fun h hh j => B.mode_vertical h hh j
    mode_bias := fun h hh j => (Real.exp_le_exp.mpr (neg_le_neg hbase)).trans_lt (B.mode_bias h hh j)
    independent := fun h hh => B.independent h hh
    test_positive := fun h hh => B.test_positive h hh
    test_complexity := fun h hh => hcomp (B.test h) (B.test_complexity h hh)
    test_invariant := fun h hh => B.test_invariant h hh
    test_violation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hbase)).trans_lt (B.test_violation h hh) }
  exact ⟨B', rfl, ⟨F.weight, F.model_layers⟩, rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

end Erdos3.PositiveShiftBasis

end

section

universe u

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_positive_basis_of_shift_failure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p epsilon : ℝ}, 0 ≤ p →
      0 ≤ epsilon → epsilon ≤ 1 → ∀ f g J : ZMod N → ℝ,
      (∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p) →
      (∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p) →
      (∀ n, 0 ≤ J n ∧ J n ≤ Real.exp p) →
      (¬ ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ Real.exp (-p) * N ∧
        CyclicNiltestShiftBound.{u} s N p (Real.exp (-p))
          (fun n => f n - (1 + epsilon) * g n) J E) →
      Nonempty (PositiveShiftBasis.{u} s N ((p + C) ^ C)
        (fun n => f n - (1 + epsilon) * g n) J) := by
  classical
  obtain ⟨c, _, hmodels⟩ := RationalFilteredNilmanifold.exists_common_model_positive_basis s
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + 2) ^ 2 + 3 + 2 * X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C c) ^ c + X + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p epsilon hp hepsilon hepsilon1 f g J hf hg hJ hfailure
  let a := fun n => f n - (1 + epsilon) * g n
  obtain ⟨H, F, hH, hlarge, hF, hviolation⟩ :=
    exists_many_positive_cyclic_violations a J (Real.exp_pos (-p)).le hfailure
  let R := fun h => Classical.choice ((hF h).model_nonempty hp)
  let L := fun h => (R h).L
  let : ∀ h, LieRing (L h) := fun h => (R h).lie
  let : ∀ h, LieAlgebra ℚ (L h) := fun h => (R h).algebra
  let : ∀ h, TopologicalSpace (ℝ ⊗[ℚ] L h) := fun h => (R h).topology
  let : ∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] L h) := fun h => (R h).topologicalAdd
  let : ∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] L h) := fun h => (R h).continuousSMul
  let : ∀ h, T2Space (ℝ ⊗[ℚ] L h) := fun h => (R h).hausdorff
  let t := raisedNiltestBudget p + 2 * p + 2
  have hraised : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  have hrt : raisedNiltestBudget p ≤ t := by dsimp [t]; linarith
  have hwt : 2 * p + 2 ≤ t := by dsimp [t]; linarith
  have hpt : p ≤ t := (le_raisedNiltestBudget p).trans hrt
  have ht : 0 ≤ t := hp.trans hpt
  have hbud : t + (t + c) ^ c + p + 2 ≤ (p + C) ^ C := by
    simpa [T, X, t, raisedNiltestBudget, Polynomial.eval₂_pow] using hbudget p hp
  have hcomp : (t + c) ^ c ≤ (p + C) ^ C := by linarith
  have hloss : p + (t + c) ^ c ≤ (p + C) ^ C := by linarith
  have hhalf : Real.exp (-((p + C) ^ C)) ≤ Real.exp (-p) / 2 := by
    have hpow : 0 ≤ (t + c) ^ c := by positivity
    exact (Real.exp_le_exp.mpr (by linarith : -((p + C) ^ C) ≤ -p - 1)).trans
      (exp_sub_one_le_half_exp (-p))
  let weight : ZMod N → ZMod N → ℂ := fun h n => ((a n * J (n + h) : ℝ) : ℂ)
  have hw (h n : ZMod N) : ‖weight h n‖ ≤ Real.exp t :=
    (shift_violation_weight_cap hepsilon hepsilon1 f g J hf hg hJ h n).trans
      (Real.exp_le_exp.mpr hwt)
  have hv (h) (hh : h ∈ H) : Real.exp (-p) <
      (𝔼 n, weight h n * (R h).test.evalCyclic N (fun _ => n)).re := by
    change Real.exp (-p) < (𝔼 n, ((a n * J (n + h) : ℝ) : ℂ) *
      (R h).test.evalCyclic N (fun _ => n)).re
    rw [real_shift_weighted_mean]
    simpa only [(R h).eval] using hviolation h hh
  obtain ⟨h₀, _, E, hE, m, H', eta, U, S, hm, _, hH', hlarge', hresult⟩ :=
    hmodels (fun h => (R h).model) (fun h => (R h).test) H hH ht
      (Real.exp_le_exp.mpr (neg_le_neg hpt))
      (fun h => (R h).complexity.mono hrt) (fun h _ => (R h).positive) weight
      (fun h _ n => hw h n) hv
  have hdensity : Real.exp (-((p + C) ^ C)) * N ≤ (H'.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(p + (t + c) ^ c)) * N :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hloss)) (Nat.cast_nonneg N)
      _ = Real.exp (-((t + c) ^ c)) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((t + c) ^ c)) * H.card :=
        mul_le_mul_of_nonneg_left hlarge.le (Real.exp_pos _).le
      _ ≤ H'.card := hlarge'
  refine ⟨{
    L := L h₀
    lie := inferInstance
    algebra := inferInstance
    dim := (R h₀).dim
    topology := inferInstance
    topologicalAdd := inferInstance
    continuousSMul := inferInstance
    hausdorff := inferInstance
    model := E
    geometry := hE.mono E hcomp
    count := m
    count_le_dim := hm
    shifts := H'
    shifts_nonempty := hH'
    shifts_large := hdensity
    frequency := eta
    mode := U
    test := S
    frequency_height := ?_
    mode_complexity := ?_
    mode_orbit := ?_
    mode_norm := ?_
    mode_vertical := ?_
    mode_bias := ?_
    independent := ?_
    test_positive := ?_
    test_complexity := ?_
    test_invariant := ?_
    test_violation := ?_ }⟩
  · exact fun h hh j i => ((hresult h hh).1 j i).trans hcomp
  · exact fun h hh j => ((hresult h hh).2.1 j).1.mono hcomp
  · exact fun h hh j => ((hresult h hh).2.1 j).2.1
  · exact fun h hh j => ((hresult h hh).2.1 j).2.2
  · exact fun h hh => (hresult h hh).2.2.1
  · intro h hh j
    have hc := (Real.exp_le_exp.mpr (neg_le_neg hcomp)).trans_lt ((hresult h hh).2.2.2.1 j)
    have he : (𝔼 n, weight h n * (U h j).evalCyclic N (fun _ => n)) =
        𝔼 n, (U h j).evalCyclic N (fun _ => n) * (a n : ℂ) * (J (n + h) : ℂ) := by
      apply Finset.expect_congr rfl
      intro n _
      dsimp only [weight]
      rw [Complex.ofReal_mul]
      ring
    simpa only [he] using hc
  · exact fun h hh => (hresult h hh).2.2.2.2.1
  · exact fun h hh => (hresult h hh).2.2.2.2.2.1
  · exact fun h hh => (hresult h hh).2.2.2.2.2.2.1.mono hcomp
  · exact fun h hh => (hresult h hh).2.2.2.2.2.2.2.1
  · intro h hh
    have hv' := hhalf.trans_lt (hresult h hh).2.2.2.2.2.2.2.2
    simpa only [weight, real_shift_weighted_mean] using hv'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RefinementPolynomialBound
namespace OAI

section

namespace Erdos3.CellRefinement

open LocalConvolution Polynomial

theorem refinementRankPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      (C : ℝ) * (1 + (3 * (C : ℝ) + 1) * p ^ 2) ^ 4 + 1 := by
  simp [refinementRankPolynomial, Polynomial.eval₂_pow]

theorem refinementDepthPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementDepthPolynomial C).eval₂ (Nat.castRingHom ℝ) p = (C : ℝ) * p + 1 := by
  simp [refinementDepthPolynomial]

theorem refinementFinalRankPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      1 + (refinementDepthPolynomial C).eval₂ (Nat.castRingHom ℝ) p *
        (refinementRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p := by
  simp [refinementFinalRankPolynomial]

theorem refinementMatchPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementMatchPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      5 * (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p +
        13 * p + 2 * (C : ℝ) + 8020 := by
  simp [refinementMatchPolynomial]

theorem refinementUnbalancedPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementUnbalancedPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      2 * (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p +
        (C : ℝ) * (1 + (3 * (C : ℝ) + 1) * p ^ 2) ^ 4 +
        2 * (C : ℝ) * p ^ 2 + 2 * p + 2 * (C : ℝ) + 3209 +
        (C : ℝ) * (3 + (3 * (C : ℝ) + 1) * p ^ 2 +
          (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p) := by
  simp [refinementUnbalancedPolynomial, Polynomial.eval₂_pow]

theorem refinementRoundPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementRoundPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      (refinementMatchPolynomial C).eval₂ (Nat.castRingHom ℝ) p +
        (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p + 3 * p + 1602 +
          (refinementUnbalancedPolynomial C).eval₂ (Nat.castRingHom ℝ) p := by
  simp [refinementRoundPolynomial]

theorem refinementWidthPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementWidthPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      (refinementDepthPolynomial C).eval₂ (Nat.castRingHom ℝ) p *
        (refinementRoundPolynomial C).eval₂ (Nat.castRingHom ℝ) p := by
  simp [refinementWidthPolynomial]

theorem refinementCostPolynomial_eval (C : ℕ) (p : ℝ) :
    (refinementCostPolynomial C).eval₂ (Nat.castRingHom ℝ) p =
      (2 * (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p + 4 * p +
        (refinementWidthPolynomial C).eval₂ (Nat.castRingHom ℝ) p +
          (refinementMatchPolynomial C).eval₂ (Nat.castRingHom ℝ) p + 1612) +
      (3 * p + 2 + (refinementFinalRankPolynomial C).eval₂ (Nat.castRingHom ℝ) p *
        ((refinementWidthPolynomial C).eval₂ (Nat.castRingHom ℝ) p +
          (refinementMatchPolynomial C).eval₂ (Nat.castRingHom ℝ) p + 10)) := by
  simp [refinementCostPolynomial]

theorem refinement_cost_le_polynomial {epsilon H p : ℝ} (hepsilon : 0 < epsilon)
    (hH : 0 ≤ H) (hp : 0 ≤ p) (C : ℕ)
    (hHC : H ≤ C)
    (hKC : CyclicCrootSisask.almostPeriodicityWidthConstant
      (localMomentGain (flatComparisonDelta epsilon) / 64) ≤ C)
    (hDC : localMomentErrorBudget (flatComparisonDelta epsilon) ≤ C)
    (hEC : unbalancedErrorBudget (localMomentGain (flatComparisonDelta epsilon)) ≤ C)
    (hgapC : 1 / (1 - refinementContraction epsilon) ≤ C) :
    let n := ⌈(p / 4) / (1 - refinementContraction epsilon)⌉₊
    let d := 1 + n * unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) p H
    refinementComparisonBudget d p (n * refinementRoundLoss d p H epsilon) epsilon ≤
      (refinementCostPolynomial C).eval₂ (Nat.castRingHom ℝ) p := by
  intro n d
  let ev := fun Q : Polynomial ℕ => Q.eval₂ (Nat.castRingHom ℝ) p
  have hev (Q : Polynomial ℕ) : 0 ≤ ev Q := natPolynomial_eval_nonneg Q hp
  have hc := localMomentGain_pos (flatComparisonDelta epsilon)
  have hgap : 0 < 1 - refinementContraction epsilon := by
    linarith [(refinementContraction_bounds epsilon).2]
  have hK : 0 ≤ CyclicCrootSisask.almostPeriodicityWidthConstant
      (localMomentGain (flatComparisonDelta epsilon) / 64) :=
    (CyclicCrootSisask.almostPeriodicityWidthConstant_pos (by positivity)).le
  have haeq : ev (refinementRankPolynomial C) =
      (C : ℝ) * (1 + (3 * (C : ℝ) + 1) * p ^ 2) ^ 4 + 1 := by
    exact refinementRankPolynomial_eval C p
  have hneq : ev (refinementDepthPolynomial C) = (C : ℝ) * p + 1 := by
    exact refinementDepthPolynomial_eval C p
  have hdeq : ev (refinementFinalRankPolynomial C) =
      1 + ev (refinementDepthPolynomial C) * ev (refinementRankPolynomial C) := by
    exact refinementFinalRankPolynomial_eval C p
  have hmeq : ev (refinementMatchPolynomial C) =
      5 * ev (refinementFinalRankPolynomial C) + 13 * p + 2 * (C : ℝ) + 8020 := by
    exact refinementMatchPolynomial_eval C p
  have hueq : ev (refinementUnbalancedPolynomial C) =
      2 * ev (refinementFinalRankPolynomial C) +
        (C : ℝ) * (1 + (3 * (C : ℝ) + 1) * p ^ 2) ^ 4 +
        2 * (C : ℝ) * p ^ 2 + 2 * p + 2 * (C : ℝ) + 3209 +
        (C : ℝ) * (3 + (3 * (C : ℝ) + 1) * p ^ 2 + ev (refinementFinalRankPolynomial C)) := by
    exact refinementUnbalancedPolynomial_eval C p
  have hleq : ev (refinementRoundPolynomial C) =
      ev (refinementMatchPolynomial C) + ev (refinementFinalRankPolynomial C) +
        3 * p + 1602 + ev (refinementUnbalancedPolynomial C) := by
    exact refinementRoundPolynomial_eval C p
  have hreq : ev (refinementWidthPolynomial C) =
      ev (refinementDepthPolynomial C) * ev (refinementRoundPolynomial C) := by
    exact refinementWidthPolynomial_eval C p
  have hqeq : ev (refinementCostPolynomial C) =
      (2 * ev (refinementFinalRankPolynomial C) + 4 * p + ev (refinementWidthPolynomial C) +
        ev (refinementMatchPolynomial C) + 1612) +
      (3 * p + 2 + ev (refinementFinalRankPolynomial C) *
        (ev (refinementWidthPolynomial C) + ev (refinementMatchPolynomial C) + 10)) := by
    exact refinementCostPolynomial_eval C p
  have ha : (unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) p H : ℝ) ≤
      ev (refinementRankPolynomial C) := by
    apply (unbalancedRankExtra_le (p := p) (H := H) hc).trans
    rw [haeq]
    gcongr
  have hn : (n : ℝ) ≤ ev (refinementDepthPolynomial C) := by
    have hceil := (Nat.ceil_lt_add_one (show 0 ≤ (p / 4) / (1 - refinementContraction epsilon)
      by positivity)).le
    have hmul := mul_le_mul_of_nonneg_right hgapC hp
    have hscale : (p / 4) / (1 - refinementContraction epsilon) ≤ (C : ℝ) * p := by
      rw [show (p / 4) / (1 - refinementContraction epsilon) =
        (1 / (1 - refinementContraction epsilon) * p) / 4 by ring]
      have hprod : 0 ≤ 1 / (1 - refinementContraction epsilon) * p := by positivity
      linarith
    rw [hneq]
    exact hceil.trans (add_le_add hscale le_rfl)
  have hd : (d : ℝ) ≤ ev (refinementFinalRankPolynomial C) := by
    rw [hdeq]
    change ((1 + n * unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) p H : ℕ) : ℝ) ≤ _
    push_cast
    exact add_le_add le_rfl (mul_le_mul hn ha (Nat.cast_nonneg _) (hev _))
  have hm : refinementMatchingLoss d p epsilon ≤ ev (refinementMatchPolynomial C) := by
    rw [hmeq]
    unfold refinementMatchingLoss
    linarith only [hd, hDC, hEC, hp]
  have hu : unbalancedWidthLoss d (localMomentGain (flatComparisonDelta epsilon)) p H ≤
      ev (refinementUnbalancedPolynomial C) := by
    apply (unbalancedWidthLoss_le_polynomial d (p := p) (H := H) hc).trans
    rw [hueq]
    gcongr
  have hl : refinementRoundLoss d p H epsilon ≤ ev (refinementRoundPolynomial C) := by
    rw [hleq]
    unfold refinementRoundLoss unbalancedReturnWidthLoss
    linarith only [hm, hd, hu, hp]
  have hl0 : 0 ≤ refinementRoundLoss d p H epsilon :=
    (by norm_num : (0 : ℝ) ≤ 2).trans (two_le_refinementRoundLoss d hp hH hepsilon)
  have hr : (n : ℝ) * refinementRoundLoss d p H epsilon ≤ ev (refinementWidthPolynomial C) := by
    rw [hreq]
    exact mul_le_mul hn hl hl0 (hev _)
  have hm0 := refinementMatchingLoss_nonneg d hp hepsilon
  have hD0 := hev (refinementFinalRankPolynomial C)
  have hR0 := hev (refinementWidthPolynomial C)
  have hM0 := hev (refinementMatchPolynomial C)
  have hprod : (d : ℝ) * ((n : ℝ) * refinementRoundLoss d p H epsilon +
      refinementMatchingLoss d p epsilon + 10) ≤ ev (refinementFinalRankPolynomial C) *
        (ev (refinementWidthPolynomial C) + ev (refinementMatchPolynomial C) + 10) := by
    gcongr
  change refinementComparisonBudget d p (n * refinementRoundLoss d p H epsilon) epsilon ≤
    ev (refinementCostPolynomial C)
  rw [hqeq]
  unfold refinementComparisonBudget
  have hprod0 : 0 ≤ ev (refinementFinalRankPolynomial C) *
      (ev (refinementWidthPolynomial C) + ev (refinementMatchPolynomial C) + 10) := by positivity
  apply max_le <;> nlinarith only [hd, hm, hr, hprod, hp, hD0, hR0, hM0, hprod0]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution

theorem exists_refinement_cost_polynomial {epsilon H : ℝ}
    (hepsilon : 0 < epsilon) (hH : 0 ≤ H) :
    ∃ Q : Polynomial ℕ, ∀ p : ℝ, 0 ≤ p →
      let n := ⌈(p / 4) / (1 - refinementContraction epsilon)⌉₊
      let d := 1 + n * unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) p H
      refinementComparisonBudget d p (n * refinementRoundLoss d p H epsilon) epsilon ≤
        Q.eval₂ (Nat.castRingHom ℝ) p := by
  let c := localMomentGain (flatComparisonDelta epsilon)
  let K := CyclicCrootSisask.almostPeriodicityWidthConstant (c / 64)
  let D := localMomentErrorBudget (flatComparisonDelta epsilon)
  let E := unbalancedErrorBudget c
  let r := 1 / (1 - refinementContraction epsilon)
  have hc : 0 < c := localMomentGain_pos _
  have hc1 : c ≤ 1 := (localMomentGain_le_half _).trans (by norm_num)
  have hK : 0 ≤ K := (CyclicCrootSisask.almostPeriodicityWidthConstant_pos (by positivity)).le
  have hD : 0 ≤ D := (localMomentErrorBudget_spec (flatComparisonDelta_spec hepsilon).1).1
  have hE : 0 ≤ E := (unbalancedErrorBudget_spec hc hc1).1
  have hr : 0 ≤ r := by
    have hgap : 0 < 1 - refinementContraction epsilon := by
      linarith [(refinementContraction_bounds epsilon).2]
    exact (one_div_pos.mpr hgap).le
  obtain ⟨C, hC⟩ := exists_nat_ge (H + K + D + E + r)
  refine ⟨refinementCostPolynomial C, ?_⟩
  intro p hp
  exact refinement_cost_le_polynomial hepsilon hH hp C
    (by linarith) (by change K ≤ C; linarith) (by change D ≤ C; linarith)
    (by change E ≤ C; linarith) (by change r ≤ C; linarith)

theorem exists_rescaled_refinement_budget {epsilon H : ℝ}
    (hepsilon : 0 < epsilon) (hH : 0 ≤ H) (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := (A : ℝ) * (p + 1)
      let n := ⌈(q / 4) / (1 - refinementContraction epsilon)⌉₊
      let d := 1 + n * unbalancedRankExtra (localMomentGain (flatComparisonDelta epsilon)) q H
      refinementComparisonBudget d q (n * refinementRoundLoss d q H epsilon) epsilon ≤
        (p + 2) ^ C := by
  obtain ⟨Q, hQ⟩ := exists_refinement_cost_polynomial hepsilon hH
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_affine_budget Q A
  refine ⟨C, hC, ?_⟩
  intro p hp
  exact (hQ ((A : ℝ) * (p + 1)) (by positivity)).trans (hbound p hp)

end Erdos3.CellRefinement

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicBilinearBound
namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators

theorem realBilinearAverage_le_of_cellBilinearBound
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {a : G → ℝ} {T : ℝ} (hT : 0 ≤ T) (hbound : CellBilinearBound Finset.univ a T)
    (f g : G → ℝ) (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1) :
    realBilinearAverage a f g ≤ T := by
  have h := hbound 0 f g hf hg (by simp) (by simp)
  have hu : 0 ≤ 𝔼 r, f r := Finset.expect_nonneg (fun r _ => (hf r).1)
  have hv : 0 ≤ 𝔼 r, g r := Finset.expect_nonneg (fun r _ => (hg r).1)
  have hu1 : (𝔼 r, f r) ≤ 1 :=
    (Finset.expect_le_expect (fun r (_ : r ∈ Finset.univ) => (hf r).2)).trans_eq
      (Finset.expect_const Finset.univ_nonempty 1)
  have hv1 : (𝔼 r, g r) ≤ 1 :=
    (Finset.expect_le_expect (fun r (_ : r ∈ Finset.univ) => (hg r).2)).trans_eq
      (Finset.expect_const Finset.univ_nonempty 1)
  have hPhi : ((𝔼 r, f r) * (𝔼 r, g r)) ^ (1 / 4 : ℝ) ≤ 1 :=
    Real.rpow_le_one (mul_nonneg hu hv) (by nlinarith) (by norm_num)
  have h' := h.trans (mul_le_mul_of_nonneg_left hPhi hT)
  simpa only [zero_add, mul_one, realBilinearAverage, bilinearIntegral] using h'

theorem exists_degree_one_bilinear_bound {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (p : ℝ), 2 ≤ p →
      ∀ A B : ZMod N → ℝ,
      (∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p) → (∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} 1 N ((p + 2) ^ C) (Real.exp (-((p + 2) ^ C))) A B →
      ∀ f g : ZMod N → ℝ, (∀ r, 0 ≤ f r ∧ f r ≤ 1) → (∀ r, 0 ≤ g r ∧ g r ≤ 1) →
      realBilinearAverage (fun r => A r - (1 + epsilon) * B r) f g ≤ Real.exp (-4 * p) := by
  obtain ⟨H, hH, hquant⟩ := exists_quantitative_bohr_bound_s2 hepsilon
  have hgap : 0 < 1 - refinementContraction epsilon := by
    linarith [(refinementContraction_bounds epsilon).2]
  have hinv : 0 ≤ 32 / (1 - refinementContraction epsilon) := by positivity
  obtain ⟨K, hK⟩ := exists_nat_ge (512 + 32 / (1 - refinementContraction epsilon))
  have hK512 : 512 ≤ K := by
    have h : (512 : ℝ) ≤ K := by linarith
    exact_mod_cast h
  have hKgap : 32 / (1 - refinementContraction epsilon) ≤ (K : ℝ) := by linarith
  obtain ⟨C, hC, hcost⟩ := exists_rescaled_refinement_budget hepsilon hH K
  refine ⟨C, hC, ?_⟩
  intro N hN p hp A B hA hB hcompare f g hf hg
  have hp0 : 0 ≤ p := by linarith
  let q := (K : ℝ) * (p + 1)
  obtain ⟨hq512, hpq, hKq⟩ := refinement_enlargement_bounds hp0 hK512
  have hqgap : 32 / (1 - refinementContraction epsilon) ≤ q := hKgap.trans hKq
  have hAq : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp q := fun r =>
    ⟨(hA r).1, (hA r).2.trans (Real.exp_le_exp.mpr hpq)⟩
  have hBq : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp q := fun r =>
    ⟨(hB r).1, (hB r).2.trans (Real.exp_le_exp.mpr hpq)⟩
  have hWcap : 2 * Real.exp p ≤ Real.exp (q / 8) :=
    refinement_enlargement_amplitude hp0 (by omega)
  have ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ 2 * Real.exp p := fun r =>
    signed_comparison_amplitude (hA r) (hB r) hepsilon.le hepsilon1.le
  have hcell := hquant N CyclicBohr.Set.whole q 0 ((p + 2) ^ C) (2 * Real.exp p)
    CyclicBohr.Set.isRankRegular_whole (by norm_num) (by norm_num) (by norm_num)
    hq512 hqgap (by norm_num) (by norm_num) A B hAq hBq (by positivity) hWcap ha hcompare
    (by simpa only [CyclicBohr.Set.rank_whole, zero_add] using hcost p hp0)
  have hwhole : CellBilinearBound Finset.univ (fun r => A r - (1 + epsilon) * B r)
      (2 * Real.exp (-q / 8)) := by
    simpa only [CyclicBohr.Set.carrier_whole] using hcell
  exact (realBilinearAverage_le_of_cellBilinearBound (by positivity) hwhole f g hf hg).trans
    (refinement_enlargement_error hp0 (by omega))

end Erdos3.CellRefinement

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeOneShiftComparison
namespace OAI

section

namespace Erdos3

theorem exists_degree_one_shift_comparison {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (p : ℝ), 2 ≤ p →
      ∀ A B J : ZMod N → ℝ,
      (∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p) → (∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p) →
      (∀ r, 0 ≤ J r ∧ J r ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} 1 N ((p + 2) ^ C) (Real.exp (-((p + 2) ^ C))) A B →
      ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ Real.exp (-p) * N ∧
        CyclicNiltestShiftBound.{0} 0 N p (Real.exp (-p))
          (fun r => A r - (1 + epsilon) * B r) J E := by
  obtain ⟨C, hC, hbilinear⟩ := CellRefinement.exists_degree_one_bilinear_bound hepsilon hepsilon1
  refine ⟨C, hC, ?_⟩
  intro N hN p hp A B J hA hB hJ hcompare
  obtain ⟨E, hE, hshifts⟩ := exists_small_bad_shift_set
    (fun r => A r - (1 + epsilon) * B r) J (by linarith) hJ
    (hbilinear N p hp A B hA hB hcompare)
  refine ⟨E, ?_, cyclicNiltestShiftBound_zero_of_constants _ _ E hshifts⟩
  simpa using hE

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FactoredPositiveShiftContradiction
namespace OAI


namespace Erdos3

theorem exists_degree_one_cyclicShiftComparison {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ c : ℕ, 2 ≤ c ∧ CyclicShiftComparison.{0} 1 epsilon c := by
  obtain ⟨c, hc, hbound⟩ := exists_degree_one_shift_comparison hepsilon hepsilon1
  refine ⟨c, hc, ?_⟩
  intro N hN p hp _ _ f g J hf hg hJ hcompare
  exact hbound N p hp f g J hf hg hJ hcompare

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AxisCompression
namespace OAI

section

universe u

namespace Erdos3

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_adapted_basis_of_shift_failure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p epsilon : ℝ}, 0 ≤ p →
      0 ≤ epsilon → epsilon ≤ 1 → ∀ f g J : ZMod N → ℝ,
      (∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p) →
      (∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p) →
      (∀ n, 0 ≤ J n ∧ J n ≤ Real.exp p) →
      (¬ ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ Real.exp (-p) * N ∧
        CyclicNiltestShiftBound.{u} s N p (Real.exp (-p))
          (fun n => f n - (1 + epsilon) * g n) J E) →
      ∃ B : PositiveShiftBasis.{u} s N ((p + C) ^ C) (fun n => f n - (1 + epsilon) * g n) J,
        ∃ weight : Fin B.dim → ℕ, ∀ i, B.model.filtration.layer i =
          Submodule.span ℚ (B.model.basis '' {j | i ≤ weight j}) := by
  obtain ⟨c, _, hbasis⟩ := exists_positive_basis_of_shift_failure s
  obtain ⟨k, _, hadapt⟩ := PositiveShiftBasis.exists_adapted
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C c) ^ c + Polynomial.C k) ^ k)
  refine ⟨C, hC, ?_⟩
  intro N _ p epsilon hp hepsilon hepsilon1 f g J hf hg hJ hfailure
  obtain ⟨B⟩ := hbasis hp hepsilon hepsilon1 f g J hf hg hJ hfailure
  obtain ⟨B', _, ⟨weight, hweight⟩, _, _, _⟩ := hadapt B
  have hbound : ((p + c) ^ c + k) ^ k ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨B'.mono hbound, weight, hweight⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u

theorem CyclicNiltestUpperComparison.mono_budget
    {degree N : ℕ} [NeZero N] {P Q epsilon delta : ℝ} {f g : ZMod N → ℝ}
    (h : CyclicNiltestUpperComparison.{u} degree N Q epsilon f g)
    (hPQ : P ≤ Q) (hdelta : epsilon ≤ delta) :
    CyclicNiltestUpperComparison.{u} degree N P delta f g := by
  intro L _ _ s dim _ _ _ _ D hs T hT hcomp
  exact (h D hs T hT (hcomp.mono hPQ)).trans hdelta

end Erdos3

end

section

namespace Erdos3

theorem exists_cyclicShiftComparison_step (s c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicShiftComparison.{0} (s + 2) epsilon C := by
  obtain ⟨A, _, hextract⟩ := exists_adapted_basis_of_shift_failure.{0} (s + 1)
  obtain ⟨B, _, hcontra⟩ :=
    PositiveShiftBasis.exists_bounded_native_contradiction_s2 s c hc hepsilon hepsilon1 hshift
  let Y : Polynomial ℕ := Polynomial.X
  let R := Y + (Y + Polynomial.C A) ^ A + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((R + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hodd hN f g J hf hg hJ hcompare
  by_contra hfailure
  obtain ⟨basis, w, hw⟩ := hextract (by linarith) hepsilon.le hepsilon1.le f g J hf hg hJ hfailure
  let q := (p + A) ^ A
  let r := p + q + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 2 ≤ r := by dsimp [r]; linarith
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hcost : (r + B) ^ B ≤ (p + 2) ^ C := by
    simpa [Y, R, q, r, Polynomial.eval₂_pow] using hbudget p (by linarith)
  have hcap (v : ZMod N → ℝ) (hv : ∀ x, 0 ≤ v x ∧ v x ≤ Real.exp p) :
      ∀ x, 0 ≤ v x ∧ v x ≤ Real.exp r :=
    fun x => ⟨(hv x).1, (hv x).2.trans (Real.exp_le_exp.mpr hpr)⟩
  exact hcontra basis w hw hr hqr hodd ((Real.exp_le_exp.mpr hcost).trans hN)
    (hcap f hf) (hcap g hg) (hcap J hJ)
    (hcompare.mono_budget hcost (Real.exp_le_exp.mpr (neg_le_neg hcost)))

theorem exists_cyclicShiftComparison_succ (s : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      ∃ C : ℕ, 2 ≤ C ∧ CyclicShiftComparison.{0} (s + 1) epsilon C := by
  induction s with
  | zero =>
    intro epsilon hepsilon hepsilon1
    exact exists_degree_one_cyclicShiftComparison hepsilon hepsilon1
  | succ s ih =>
    intro epsilon hepsilon hepsilon1
    obtain ⟨c, hc, hshift⟩ := ih (epsilon / 2) (by linarith) (by linarith)
    exact exists_cyclicShiftComparison_step s c hc hepsilon hepsilon1 hshift

theorem exists_cyclicShiftComparison_positive_s2_oai (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicShiftComparison.{0} s epsilon C := by
  cases s with
  | zero => omega
  | succ s => exact exists_cyclicShiftComparison_succ s epsilon hepsilon hepsilon1

end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.exists_cyclicShiftComparison_positive_s2_oai := @OAI.Erdos3.exists_cyclicShiftComparison_positive_s2_oai

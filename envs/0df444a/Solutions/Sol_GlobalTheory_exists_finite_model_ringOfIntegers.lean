-- Prove2me | solution 1 for GlobalTheory.exists_finite_model_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:20.283321+00:00
-- url     : https://prove2.me/submissions/8e1e5bc8-3d0d-4bd0-a6cc-8decd8659dea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Theorems.Thm_GlobalTheory_exists_model_ringOfIntegers
import Theorems.Thm_GlobalTheory_exists_finite_hasRationalTorsion_twelve

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GlobalTheory
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic] (hj : IsIntegral ℤ W.j) :
    ∃ M : IntermediateField K (AlgebraicClosure K), NumberField M ∧
      HasRationalTorsion (W.baseChange M) (AlgebraicClosure K) 12 ∧
      ∃ (C : VariableChange M) (W₀ : WeierstrassCurve (𝓞 M)),
        C • W.baseChange M = W₀.baseChange M ∧ W₀.Δ = 1 := by
  obtain ⟨M, hM, h⟩ := exists_finite_hasRationalTorsion_twelve W (AlgebraicClosure K)
  have : NumberField M := NumberField.of_module_finite K M
  have : (W.baseChange M).IsElliptic := inferInstanceAs (W.map (algebraMap K M)).IsElliptic
  have hj' : IsIntegral ℤ (W.baseChange M).j := by
    rw [show (W.baseChange M).j = algebraMap K M W.j from W.map_j _]
    exact hj.algebraMap
  exact ⟨M, inferInstance, h, exists_model_ringOfIntegers hj' h M⟩
end GlobalTheory

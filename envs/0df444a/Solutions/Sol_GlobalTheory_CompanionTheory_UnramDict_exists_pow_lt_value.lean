-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnramDict.exists_pow_lt_value
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:55.064865+00:00
-- url     : https://prove2.me/submissions/9accf0a6-5f37-4adc-83a4-4bf9ea9479f7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Topology Filter
open PositivityTheory.Rg.Tf.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnramDict
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GlobalTheory.CompanionTheory.UnramDict
theorem _root_.solution {a γ : ValueGroupWithZero K} (ha : a < 1) (hγ : γ ≠ 0) :
    ∃ m : ℕ, a ^ m < γ := by
  have e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have : MulArchimedean (ValueGroupWithZero K) := .comap e.toMonoidHom e.strictMono
  exact exists_pow_lt₀ ha (Units.mk0 γ hγ)
end GlobalTheory.CompanionTheory.UnramDict

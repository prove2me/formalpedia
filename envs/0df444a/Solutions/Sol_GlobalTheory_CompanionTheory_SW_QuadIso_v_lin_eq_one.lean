-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadIso.v_lin_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:54:52.687229+00:00
-- url     : https://prove2.me/submissions/661aa31f-72ca-4843-9613-a40e4ec371cd

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHaarQuadraticSubstitutionInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix WithZero
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadIso
variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
namespace GlobalTheory.CompanionTheory.SW.QuadIso
theorem _root_.solution {a c s : K} (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1)
    (hs : Valued.v s < 1) : Valued.v (a + c * s) = 1 := by
  have : Valued.v (c * s) < Valued.v a := by
    rw [ha, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hs
  rw [Valuation.map_add_eq_of_lt_left _ this, ha]
end GlobalTheory.CompanionTheory.SW.QuadIso

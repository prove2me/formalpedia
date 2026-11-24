-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadIso.v_quad_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:10:50.276528+00:00
-- url     : https://prove2.me/submissions/7e5afd9a-99ba-4a75-8652-675e2e9b4a37

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHaarQuadraticSubstitutionInvariant
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_quad_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_v_lin_eq_one

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
theorem _root_.solution {a c t t' : K} (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1)
    (ht : Valued.v t < 1) (ht' : Valued.v t' < 1) :
    Valued.v ((a * t + c * t ^ 2) - (a * t' + c * t' ^ 2)) = Valued.v (t - t') := by
  rw [quad_sub, map_mul, v_lin_eq_one ha hc (Valuation.map_add_lt _ ht ht'), mul_one]
end GlobalTheory.CompanionTheory.SW.QuadIso

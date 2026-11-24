-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HermRep.hE_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:24:10.48029+00:00
-- url     : https://prove2.me/submissions/fcce045f-2f07-4556-b384-b75c686d00a5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_EqIdOfFixed
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermRep
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (T : Matrix (Fin M) (Fin M) E)
namespace GlobalTheory.CompanionTheory.SW.HermRep
theorem _root_.solution (x y y' : Fin M → E) :
    hE σ T x (y + y') = hE σ T x y + hE σ T x y' := by
  simp only [hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
end GlobalTheory.CompanionTheory.SW.HermRep

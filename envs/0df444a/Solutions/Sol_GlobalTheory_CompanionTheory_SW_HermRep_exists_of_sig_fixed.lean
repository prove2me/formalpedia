-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HermRep.exists_of_sig_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:24:09.028305+00:00
-- url     : https://prove2.me/submissions/b5791ea6-e3fa-4a30-8982-949d0e759c3f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_EqIdOfFixed
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar
import Theorems.Thm_Bl_EqIdOfFixed_goal1


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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
namespace GlobalTheory.CompanionTheory.SW.HermRep
theorem _root_.solution (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    ∃ t : F, algebraMap F E t = x :=
  _root_.Bl.EqIdOfFixed.goal1 h hx
end GlobalTheory.CompanionTheory.SW.HermRep

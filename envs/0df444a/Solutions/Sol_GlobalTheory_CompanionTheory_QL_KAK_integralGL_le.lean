-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.KAK.integralGL_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:00:16.2527+00:00
-- url     : https://prove2.me/submissions/606bbdf0-68e5-4de2-9525-a4c27a6bc3da

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartanDecompositionGeneralLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.KAK
variable {F : Type} [Field F]
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.CompanionTheory.QL.KAK
theorem _root_.solution (n : ℕ) :
    GroundTheory.Automorphic.GLnLocal.integralGL F n ≤ GLint 𝒪[F] n := fun _ hg =>
  (GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff F n).1 hg
end GlobalTheory.CompanionTheory.QL.KAK

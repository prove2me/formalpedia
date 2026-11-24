-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Inh.CharId.IsPolyFun.scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:38:22.393368+00:00
-- url     : https://prove2.me/submissions/0528325c-fca3-4a17-a86a-f28a0d58aed4

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_CharacteristicIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset TensorProduct Formalism.HermitianLatticeCounting.S8
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Inh GlobalTheory.CompanionTheory.Inh.CharId
open Polynomial Formalism.REAL
variable {B : Type*} [Ring B] [Algebra ℂ B]
namespace GlobalTheory.CompanionTheory.Inh.CharId
namespace IsPolyFun
theorem _root_.solution : IsPolyFun (fun u => algebraMap ℂ B u) := ⟨X, fun u => by simp⟩
end IsPolyFun
end GlobalTheory.CompanionTheory.Inh.CharId

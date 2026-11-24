-- Prove2me | solution 1 for GlobalTheory.HTLat.grLat_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:11:11.469773+00:00
-- url     : https://prove2.me/submissions/1e4c4786-8369-41ac-a936-d3cf25b93ee0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U]
namespace GlobalTheory.HTLat
theorem _root_.solution (La : Submodule O U) (F' F : Submodule C U) :
    grLat La F' F ≤ (F.map F'.mkQ).restrictScalars O := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx.2, rfl⟩
end GlobalTheory.HTLat

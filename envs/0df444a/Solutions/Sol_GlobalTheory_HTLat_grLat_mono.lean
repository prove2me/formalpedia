-- Prove2me | solution 1 for GlobalTheory.HTLat.grLat_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:51:54.158121+00:00
-- url     : https://prove2.me/submissions/ce656b6c-ef22-4dca-a465-5a86bc5f5c1e

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
theorem _root_.solution {La La' : Submodule O U} (h : La ≤ La') (F' F : Submodule C U) :
    grLat La F' F ≤ grLat La' F' F := Submodule.map_mono (inf_le_inf_right _ h)
end GlobalTheory.HTLat

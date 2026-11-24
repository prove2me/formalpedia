-- Prove2me | solution 1 for GlobalTheory.FunObj.idxRatio_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:52:39.715516+00:00
-- url     : https://prove2.me/submissions/1d6442c4-c87a-4f9a-b196-3ffad5f11bfd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InverseUnipotentVolumeConjDiagonalUnitsGLMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open Matrix
variable {G : Type*} [Group G]
namespace GlobalTheory.FunObj
theorem _root_.solution {f : G →* G} (hf : Function.Injective f) (A B : Subgroup G) :
    idxRatio (A.map f) (B.map f) = idxRatio A B := by
  rw [idxRatio, idxRatio, Subgroup.relIndex_map_map_of_injective _ _ hf,
    Subgroup.relIndex_map_map_of_injective _ _ hf]
end GlobalTheory.FunObj

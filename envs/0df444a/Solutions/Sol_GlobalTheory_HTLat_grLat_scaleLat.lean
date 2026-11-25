-- Prove2me | solution 1 for GlobalTheory.HTLat.grLat_scaleLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:49:41.686544+00:00
-- url     : https://prove2.me/submissions/af9d497d-376d-43d7-9552-840a26ee165f

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
theorem _root_.solution {a : C} (ha : a ≠ 0) (La : Submodule O U) (F' F : Submodule C U) :
    grLat (scaleLat a La) F' F = scaleLat a (grLat La F' F) := by
  ext z
  constructor
  · rintro ⟨_, ⟨⟨y, hy, rfl⟩, hF⟩, rfl⟩
    exact ⟨F'.mkQ y, ⟨y, ⟨hy, (F.smul_mem_iff ha).1 hF⟩, rfl⟩, (map_smul F'.mkQ a y).symm⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨a • y, ⟨⟨y, hy.1, rfl⟩, F.smul_mem a hy.2⟩, map_smul F'.mkQ a y⟩
end GlobalTheory.HTLat

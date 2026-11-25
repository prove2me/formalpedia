-- Prove2me | solution 1 for GlobalTheory.HL.ncard_stabilizer_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:32:43.028287+00:00
-- url     : https://prove2.me/submissions/a944f5c2-fa8c-4cc4-af45-39cd9c64d78c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormOrbitSumLeOfSymmKernel
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL
variable {G X : Type} [Group G] [MulAction G X] (St : Subgroup G)
namespace GlobalTheory.HL
theorem _root_.solution (y w : X) :
    {w' | ∃ h ∈ St, h • y = y ∧ h • w = w'}.ncard =
      (St ⊓ MulAction.stabilizer G w).relIndex (St ⊓ MulAction.stabilizer G y) := by
  have h1 : {w' | ∃ h ∈ St, h • y = y ∧ h • w = w'} =
      MulAction.orbit (St ⊓ MulAction.stabilizer G y : Subgroup G) w := by
    ext w'
    constructor
    · rintro ⟨h, h1, h2, h3⟩
      exact ⟨⟨h, h1, h2⟩, h3⟩
    · rintro ⟨⟨h, h1, h2⟩, h3⟩
      exact ⟨h, h1, h2, h3⟩
  rw [h1, ← MulAction.index_stabilizer, Subgroup.relIndex]
  congr 1
  ext ⟨h, h1, h2⟩
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h3 => ⟨h1, h3⟩, fun h3 => h3.2⟩
end GlobalTheory.HL

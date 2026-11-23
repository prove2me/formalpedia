-- Prove2me | solution 1 for GlobalTheory.BI.isIrreducible_transportRep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:06.132071+00:00
-- url     : https://prove2.me/submissions/4d58cf36-efa6-444a-a9d1-acfdff9dea73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.BI
variable {K G V W : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
namespace GlobalTheory.BI
theorem _root_.solution (ρ : Representation K G V) (e : V ≃ₗ[K] W)
    (h : ρ.IsIrreducible) : (transportRep ρ e).IsIrreducible := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  exact (transportSubOrderIso ρ e).isSimpleOrder
end GlobalTheory.BI

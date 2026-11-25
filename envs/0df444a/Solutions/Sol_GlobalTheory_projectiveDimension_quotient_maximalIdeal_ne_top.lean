-- Prove2me | solution 1 for GlobalTheory.projectiveDimension_quotient_maximalIdeal_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:11.611706+00:00
-- url     : https://prove2.me/submissions/05f8648b-d979-4744-85f8-10660205f8cf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory IsLocalRing
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution (R : Type u) [CommRing R]
    [IsRegularLocalRing R] :
    projectiveDimension (ModuleCat.of R (R ⧸ maximalIdeal R)) ≠ ⊤ := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  have hreg := isRegular_of_ofList_eq_maximalIdeal h hd.le
  have key := ModuleCat.projectiveDimension_quotient_eq_length.{u} xs hreg
  rw [projectiveDimension_eq_of_iso (Shrink.linearEquiv R _).toModuleIso, h] at key
  rw [key]
  exact ne_of_beq_false rfl
end GlobalTheory

-- Prove2me | solution 1 for GroundTheory.LocalField.maximalAbelianExtension_eq_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:48:10.980711+00:00
-- url     : https://prove2.me/submissions/22b9bc0c-a51f-4406-95b1-e7213d671d40

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
import Theorems.Thm_GroundTheory_LocalField_exists_finite_abelian_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open IntermediateField
open scoped commutatorElement
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
namespace GroundTheory.LocalField
theorem _root_.solution :
    maximalAbelianExtension F Ω =
      ⨆ (L : IntermediateField F Ω) (_ : FiniteDimensional F L) (_ : IsAbelianGalois F L), L := by
  refine le_antisymm (fun y hy => ?_) (iSup_le fun L => iSup_le fun _ => iSup_le fun _ =>
    le_maximalAbelianExtension L)
  obtain ⟨L, hL1, hL2, hyL⟩ := exists_finite_abelian_mem hy
  have hle : L ≤ ⨆ (L : IntermediateField F Ω) (_ : FiniteDimensional F L) (_ : IsAbelianGalois F L), L :=
    le_iSup_of_le L (le_iSup_of_le hL1 (le_iSup_of_le hL2 le_rfl))
  exact hle hyL
end GroundTheory.LocalField

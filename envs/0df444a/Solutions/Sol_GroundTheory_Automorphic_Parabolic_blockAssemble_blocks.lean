-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.blockAssemble_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:50:57.467257+00:00
-- url     : https://prove2.me/submissions/122e4810-d6ef-43bb-8d49-174e2b542e38

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockAssemble_apply_of_eq
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockAssemble_apply_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel
variable {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable (R : Type*) [CommRing R]
variable {β R}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {X : Matrix (Fin n) (Fin n) R}
    (hX : ∀ i j, β i ≠ β j → X i j = 0) : blockAssemble β R (blocks β R X) = X := by
  ext i j
  by_cases h : β i = β j
  · have hj : blockOf β j = blockOf β i := Subtype.ext h.symm
    rw [blockAssemble_apply_of_eq _ rfl hj]
    rfl
  · rw [blockAssemble_apply_of_ne _ h, hX i j h]
end GroundTheory.Automorphic.Parabolic

-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.blockAssemble_apply_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:41:54.445209+00:00
-- url     : https://prove2.me/submissions/01440b47-64a7-4a27-9942-a16937b8c9a1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_sigmaFiberEquiv_symm_eq
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockAssemble_apply

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
theorem _root_.solution (X : ∀ a : Set.range β, Matrix (Fiber β a) (Fiber β a) R)
    {i j : Fin n} (h : β i ≠ β j) : blockAssemble β R X i j = 0 := by
  rw [blockAssemble_apply, sigmaFiberEquiv_symm_eq rfl, sigmaFiberEquiv_symm_eq rfl]
  exact blockDiagonal'_apply_ne _ _ _ fun e => h (congrArg Subtype.val e)
end GroundTheory.Automorphic.Parabolic

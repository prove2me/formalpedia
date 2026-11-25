-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.blockAssemble_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:32:03.344619+00:00
-- url     : https://prove2.me/submissions/2bf4cfda-7097-4c2e-8a42-30076b3bb1be

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan

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
    (i j : Fin n) :
    blockAssemble β R X i j = blockDiagonal' X ((Equiv.sigmaFiberEquiv (blockOf β)).symm i)
      ((Equiv.sigmaFiberEquiv (blockOf β)).symm j) := rfl
end GroundTheory.Automorphic.Parabolic

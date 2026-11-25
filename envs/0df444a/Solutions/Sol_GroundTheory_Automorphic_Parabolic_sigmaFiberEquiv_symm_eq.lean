-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.sigmaFiberEquiv_symm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:31:38.984596+00:00
-- url     : https://prove2.me/submissions/4b92b95a-e583-406c-a017-7b7eb9698ec4

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
theorem _root_.solution {i : Fin n} {a : Set.range β} (hi : blockOf β i = a) :
    (Equiv.sigmaFiberEquiv (blockOf β)).symm i = ⟨a, ⟨i, hi⟩⟩ := by
  subst hi
  rfl
end GroundTheory.Automorphic.Parabolic

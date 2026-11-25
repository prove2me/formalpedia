-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.blockAssemble_apply_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:41:52.148444+00:00
-- url     : https://prove2.me/submissions/3e94880e-d843-4027-be7f-3d904e3ff930

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
    {i j : Fin n} {a : Set.range β} (hi : blockOf β i = a) (hj : blockOf β j = a) :
    blockAssemble β R X i j = X a ⟨i, hi⟩ ⟨j, hj⟩ := by
  rw [blockAssemble_apply, sigmaFiberEquiv_symm_eq hi, sigmaFiberEquiv_symm_eq hj,
    blockDiagonal'_apply_eq]
end GroundTheory.Automorphic.Parabolic

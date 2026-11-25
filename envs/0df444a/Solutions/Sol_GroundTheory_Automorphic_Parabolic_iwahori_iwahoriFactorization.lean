-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.iwahori_iwahoriFactorization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:27:30.647799+00:00
-- url     : https://prove2.me/submissions/a83b2dee-c2c8-43f2-b8e1-0a17a0d24fe4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_iwahoriFactorization_of_elim
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_diag_ne_zero_of_mem_iwahori
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_mem_iwahori
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_elimGL_mem_iwahori

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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
local notation "ϖ" => ((GLnLocal.uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hβ : Monotone β) :
    ∀ k ∈ iwahori F n, ∃ z ∈ iwahori F n ⊓ oppositeUnipotentRadical F n β,
      ∃ y ∈ iwahori F n ⊓ levi F n β, ∃ x ∈ iwahori F n ⊓ unipotentRadical F n β,
        k = z * y * x :=
  iwahoriFactorization_of_elim _ (fun _ hh a => diag_ne_zero_of_mem_iwahori hh a)
    (fun _ hh a => elimGL_mem_iwahori hβ hh a)
    (fun _ hp hpI => leviProj_mem_iwahori hp hpI)
    (fun _ hp hpI => leviProj_mem_iwahori hp hpI)
end GroundTheory.Automorphic.Parabolic

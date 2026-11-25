-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.congruenceSubgroup_iwahoriFactorization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:26:03.739641+00:00
-- url     : https://prove2.me/submissions/ace38a7e-5f63-46f3-a6ad-05991ca3530a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_iwahoriFactorization_of_elim
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_diag_ne_zero_of_mem_congruenceSubgroup
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_elimGL_mem_congruenceSubgroup
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_mem_congruenceSubgroup

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
variable (β)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    ∀ k ∈ congruenceSubgroup F n m,
      ∃ z ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β,
      ∃ y ∈ congruenceSubgroup F n m ⊓ levi F n β,
      ∃ x ∈ congruenceSubgroup F n m ⊓ unipotentRadical F n β, k = z * y * x :=
  iwahoriFactorization_of_elim _ (fun _ hh a => diag_ne_zero_of_mem_congruenceSubgroup hm hh a)
    (fun _ hh a => elimGL_mem_congruenceSubgroup hm hh a)
    (fun _ hp hpK => leviProj_mem_congruenceSubgroup hp hpK)
    (fun _ hp hpK => leviProj_mem_congruenceSubgroup hp hpK)
end GroundTheory.Automorphic.Parabolic

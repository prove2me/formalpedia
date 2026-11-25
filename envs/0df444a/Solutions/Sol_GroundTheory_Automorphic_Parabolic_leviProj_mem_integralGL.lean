-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.leviProj_mem_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:02.460917+00:00
-- url     : https://prove2.me/submissions/89856263-8f4a-41c3-974e-0829cc3d693d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Theorems.Thm_P2M_GroundTheory_Automorphic_Parabolic_leviProj_mem_congruenceSubgroup__c7c7a3a01a19
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_zero
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_EntryBound_leviProj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {α : Type*} [LinearOrder α] {β : Fin n → α}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {p : blockUpper F n β}
    (hp : (p : GL (Fin n) F) ∈ integralGL F n) :
    ((leviProj F n β p : levi F n β) : GL (Fin n) F) ∈ integralGL F n := by
  rw [← congruenceSubgroup_zero] at hp ⊢
  exact leviProj_mem_congruenceSubgroup' hp
end GroundTheory.Automorphic.Parabolic

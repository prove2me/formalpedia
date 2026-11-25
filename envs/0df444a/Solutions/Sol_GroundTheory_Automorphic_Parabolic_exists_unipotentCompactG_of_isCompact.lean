-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_unipotentCompactG_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:44.824332+00:00
-- url     : https://prove2.me/submissions/04c9d4a8-0f2d-4c99-8ada-0f084e4046d7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_entryBound_of_isCompact
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentCompactG_of_bound


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
variable {γ : Fin n → ℕ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {S : Set (GL (Fin n) F)} (hS : IsCompact S)
    (hSN : S ⊆ unipotentRadical F n γ) :
    ∃ e : ℕ, S ⊆ (unipotentCompactG (F := F) γ e : Set (GL (Fin n) F)) := by
  obtain ⟨e, he⟩ := entryBound_of_isCompact hS
  exact ⟨e, fun u hu => mem_unipotentCompactG_of_bound (hSN hu) (he u hu).1 (he u hu).2⟩
end GroundTheory.Automorphic.Parabolic

-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.closure_doubleCoset_subset_of_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:33:59.569033+00:00
-- url     : https://prove2.me/submissions/5ba0cf0a-c773-496e-a8a3-60c78000a8e3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellHeight_of_mem_doubleCoset
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_closure_doubleCoset_subset


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
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T1Space F] {n : ℕ}
  {β γ : Fin n → ℕ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {k : ℕ} {w : Fin k → Equiv.Perm (Fin n)}
    (hcov : ∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j))
      (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ))
    (hanti : Antitone fun j => cellHeight β γ (permGL F (w j))) (j : Fin k) :
    closure (doubleCoset (permGL F (w j)) (blockUpper F n β : Set (GL (Fin n) F))
        (blockUpper F n γ)) ⊆
      ⋃ l : Fin k, ⋃ (_ : j ≤ l), doubleCoset (permGL F (w l))
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ) := by
  intro x hx
  obtain ⟨l, hl, -⟩ := hcov x
  refine mem_iUnion₂.2 ⟨l, ?_, hl⟩
  rcases closure_doubleCoset_subset _ hx with h | h
  · obtain ⟨j', -, hu⟩ := hcov x
    have h1 := hu j h
    have h2 := hu l hl
    rw [h1, h2]
  · by_contra hjl
    have := hanti (le_of_lt (not_le.1 hjl))
    rw [Set.mem_ofPred_eq, cellHeight_of_mem_doubleCoset hl] at h
    exact absurd this (not_le.2 h)
end GroundTheory.Automorphic.Parabolic

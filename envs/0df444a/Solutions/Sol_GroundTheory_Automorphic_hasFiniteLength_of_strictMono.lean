-- Prove2me | solution 1 for GroundTheory.Automorphic.hasFiniteLength_of_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:57.188158+00:00
-- url     : https://prove2.me/submissions/061417c2-144f-4bea-986b-0863e08c6144

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Theorems.Thm_GroundTheory_Automorphic_hasFiniteLength_iff
import Theorems.Thm_GroundTheory_Automorphic_HasFiniteLength_wellFoundedLT
import Theorems.Thm_GroundTheory_Automorphic_HasFiniteLength_wellFoundedGT

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
open Function
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic
theorem _root_.solution {ι : Type*} [Finite ι] {α : ι → Type*}
    [∀ i, PartialOrder (α i)] [∀ i, WellFoundedLT (α i)] [∀ i, WellFoundedGT (α i)]
    (Λ : Subrepresentation ρ → ∀ i, α i) (hΛ : StrictMono Λ) : HasFiniteLength ρ := by
  rw [hasFiniteLength_iff]
  refine ⟨hΛ.wellFoundedLT, ?_⟩
  have h1 : WellFoundedLT (∀ i, (α i)ᵒᵈ) := Pi.wellFoundedLT
  have h2 : WellFoundedGT (∀ i, α i) := ⟨h1.wf⟩
  exact hΛ.wellFoundedGT
end GroundTheory.Automorphic

-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.mem_of_mem_genSubrep_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:59:28.47228+00:00
-- url     : https://prove2.me/submissions/20c96c0b-6763-4f7c-8597-912e4e8113c3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_of_mem


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
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [LocallyCompactSpace L] [T2Space L] [TotallyDisconnectedSpace L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {σ : Representation ℂ L V}
variable (hσ : IsSmooth σ) {K : Subgroup L} (hKc : IsCompact (K : Set L))
  (hKo : IsOpen (K : Set L)) (N : Submodule ℂ V)
variable {N}
variable (hNK : N ≤ fixedVectors σ K)
  (hNst : ∀ g, ∀ n ∈ N, (fixedProj σ hσ hKc hKo (σ g n) : V) ∈ N)
include hNK hNst
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {u : V} (hu : u ∈ (genSubrep σ N).toSubmodule)
    (huK : u ∈ fixedVectors σ K) : u ∈ N := by
  have h1 : (fixedProj σ hσ hKc hKo u : V) = u := fixedProj_apply_of_mem hσ hKc hKo huK
  rw [← h1]
  have : (genSubrep σ N).toSubmodule ≤ N.comap ((fixedVectors σ K).subtype ∘ₗ
      fixedProj σ hσ hKc hKo) := by
    refine iSup_le fun g => ?_
    rintro _ ⟨n, hn, rfl⟩
    exact hNst g n hn
  exact this hu
end GroundTheory.Automorphic.RestrictedTensor

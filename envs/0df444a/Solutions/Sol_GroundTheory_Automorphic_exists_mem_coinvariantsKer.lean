-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_mem_coinvariantsKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:44:40.930238+00:00
-- url     : https://prove2.me/submissions/295e92c4-f21a-4896-b16d-8570962ba5c8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet

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
open Set Filter Topology
variable {N : Type*} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  [LocallyCompactSpace N] [T2Space N] [TotallyDisconnectedSpace N]
  {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ N V)
omit [IsTopologicalGroup N] [LocallyCompactSpace N] [T2Space N] [TotallyDisconnectedSpace N]
namespace GroundTheory.Automorphic
theorem _root_.solution
    (hN : ∀ s : Finset N, ∃ K : Subgroup N, IsCompact (K : Set N) ∧ IsOpen (K : Set N) ∧
      ∀ x ∈ s, x ∈ K)
    {v : V} (hv : v ∈ Representation.Coinvariants.ker ρ) :
    ∃ K : Subgroup N, IsCompact (K : Set N) ∧ IsOpen (K : Set N) ∧ v ∈ coinvariantsKer ρ K := by
  classical
  obtain ⟨T, hT, hvT⟩ := Submodule.mem_span_finite_of_mem_span hv
  have : ∀ t ∈ T, ∃ g : N, ∃ w : V, ρ g w - w = t := fun t ht => by
    obtain ⟨⟨g, w⟩, h⟩ := hT ht
    exact ⟨g, w, h⟩
  choose! gf wf hgf using this
  obtain ⟨K, hKc, hKo, hK⟩ := hN (T.image gf)
  refine ⟨K, hKc, hKo, Submodule.span_le.2 (fun t ht => ?_) hvT⟩
  rw [← hgf t ht]
  exact sub_mem_coinvariantsKer (hK _ (Finset.mem_image_of_mem gf ht)) (wf t)
end GroundTheory.Automorphic

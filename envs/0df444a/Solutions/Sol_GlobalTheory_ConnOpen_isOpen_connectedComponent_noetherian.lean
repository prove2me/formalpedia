-- Prove2me | solution 1 for GlobalTheory.ConnOpen.isOpen_connectedComponent_noetherian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:57:19.121688+00:00
-- url     : https://prove2.me/submissions/f7135a4a-f98c-44a8-9f41-d1172972f19e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenConnectedComponentOfIsLocallyNoetherian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConnOpen
namespace GlobalTheory.ConnOpen
theorem _root_.solution {Y : Type*} [TopologicalSpace Y] [NoetherianSpace Y] (y : Y) :
    IsOpen (connectedComponent y) := by
  set C := connectedComponent y
  have key : ∀ t, t ∉ C → irreducibleComponent t ⊆ Cᶜ := by
    intro t ht s hs hsC
    have h1 : irreducibleComponent t ⊆ connectedComponent s :=
      _root_.IsPreconnected.subset_connectedComponent
        (isIrreducible_irreducibleComponent (x := t)).isConnected.isPreconnected hs
    rw [← connectedComponent_eq hsC] at h1
    exact ht (h1 mem_irreducibleComponent)
  have hC : Cᶜ = ⋃ Z ∈ {Z ∈ irreducibleComponents Y | Z ⊆ Cᶜ}, Z := by
    ext t
    refine ⟨fun ht => Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents t, key t ht⟩
      mem_irreducibleComponent, fun ht => ?_⟩
    obtain ⟨Z, ⟨-, hZ⟩, htZ⟩ := Set.mem_iUnion₂.1 ht
    exact hZ htZ
  have hcl : IsClosed Cᶜ := by
    rw [hC]
    exact (NoetherianSpace.finite_irreducibleComponents.subset fun _ h => h.1).isClosed_biUnion
      fun Z h => isClosed_of_mem_irreducibleComponents Z h.1
  exact isClosed_compl_iff.1 hcl
end GlobalTheory.ConnOpen

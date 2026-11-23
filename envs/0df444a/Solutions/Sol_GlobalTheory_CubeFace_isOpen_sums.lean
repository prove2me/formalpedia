-- Prove2me | solution 1 for GlobalTheory.CubeFace.isOpen_sums
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:39.433585+00:00
-- url     : https://prove2.me/submissions/5ba1af5b-f985-4268-baa4-9d0c9e45621e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.CubeFace
namespace GlobalTheory.CubeFace
theorem _root_.solution {g : ℕ} {ι : Type} (W : ι → Set (Fin g → ℂ)) (hW : ∀ i, IsOpen (W i))
    (j : Finset (Fin 3) → ι) :
    IsOpen {x : Fin 3 → Fin g → ℂ | ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)} := by
  rw [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun I => ?_
  exact (hW _).preimage (f := fun x : Fin 3 → Fin g → ℂ => ∑ a ∈ I, x a) (by fun_prop)
end GlobalTheory.CubeFace

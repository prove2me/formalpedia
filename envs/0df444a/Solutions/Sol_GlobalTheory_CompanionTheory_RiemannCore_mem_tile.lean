-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RiemannCore.mem_tile
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:25.701686+00:00
-- url     : https://prove2.me/submissions/563769dc-f4b2-49e9-9dae-4d4ec1eff0cf

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RiemannCore
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G]
namespace GlobalTheory.CompanionTheory.RiemannCore
theorem _root_.solution {D : Set G} {R : Finset G} {l y : G} :
    y ∈ tile D R l ↔ ∃ r ∈ R, y - r - l ∈ D := by
  simp only [tile, cell, Set.mem_preimage, Set.mem_iUnion, exists_prop]
  refine exists_congr fun r => and_congr Iff.rfl ?_
  have : -r + (-l + y) = y - r - l := by abel
  rw [this]
end GlobalTheory.CompanionTheory.RiemannCore

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RiemannCore.tile_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:09:40.813199+00:00
-- url     : https://prove2.me/submissions/3846481e-ea60-4256-b6be-bc8e97fbd2ca

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScaling
import Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_mem_tile

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
theorem _root_.solution {D : Set G} {R : Finset G} {Λ : AddSubgroup G}
    (ht : ∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) :
    ⋃ l : Λ, tile D R (l : G) = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨⟨r, l⟩, ⟨hr, hl, h⟩, -⟩ := ht y
  exact Set.mem_iUnion.2 ⟨⟨l, hl⟩, mem_tile.2 ⟨r, hr, h⟩⟩
end GlobalTheory.CompanionTheory.RiemannCore

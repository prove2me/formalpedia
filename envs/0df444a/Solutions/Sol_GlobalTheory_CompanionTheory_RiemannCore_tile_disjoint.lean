-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RiemannCore.tile_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:32.419452+00:00
-- url     : https://prove2.me/submissions/334ae337-8f3f-4eb1-b534-6537da207adf

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
    Pairwise (Function.onFun Disjoint fun l : Λ => tile D R (l : G)) := by
  intro l l' hne
  refine Set.disjoint_left.2 fun y hy hy' => hne ?_
  obtain ⟨r, hr, h⟩ := mem_tile.1 hy
  obtain ⟨r', hr', h'⟩ := mem_tile.1 hy'
  have := (ht y).unique (y₁ := (r, (l : G))) (y₂ := (r', (l' : G))) ⟨hr, l.2, h⟩ ⟨hr', l'.2, h'⟩
  exact Subtype.ext (congrArg Prod.snd this)
end GlobalTheory.CompanionTheory.RiemannCore

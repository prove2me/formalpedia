-- Prove2me | solution 1 for GlobalTheory.isOpen_component_fibre_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:21:22.911231+00:00
-- url     : https://prove2.me/submissions/86930c5b-36be-44cc-9629-02271a9be28a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenConnectedComponentOfIsLocallyNoetherianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothGenericFibreClosurePartitionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionMemComponentGenericOfClosedValuation
import Theorems.Thm_P2M_GlobalTheory_T_isOpen_connectedComponent_of_isLocallyNoetherian__f7bb4608baf5


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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X S : Scheme.{0}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (s : S) (a : (f ⁻¹' {s} : Set X)) : IsOpen (connectedComponent a) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s)))
  have hn : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  have ho := GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' _ hn ((f.fiberHomeo s).symm a)
  have h := (f.fiberHomeo s).isOpenMap _ ho
  have h2 : (f.fiberHomeo s) '' connectedComponent ((f.fiberHomeo s).symm a)
      = connectedComponent a := by
    have := (f.fiberHomeo s).image_connectedComponentIn (s := Set.univ)
      (x := (f.fiberHomeo s).symm a) (Set.mem_univ _)
    simpa [connectedComponentIn_univ, (f.fiberHomeo s).surjective.range_eq] using this
  rwa [h2] at h
end GlobalTheory

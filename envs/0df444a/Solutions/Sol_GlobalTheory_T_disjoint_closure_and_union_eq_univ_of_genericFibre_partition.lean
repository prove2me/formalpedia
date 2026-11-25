-- Prove2me | solution 1 for GlobalTheory.T.disjoint_closure_and_union_eq_univ_of_genericFibre_partition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:20.220938+00:00
-- url     : https://prove2.me/submissions/56b341a4-9e42-43c2-8215-2f0bfac647bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothGenericFibreClosurePartition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothGenericFibreClosurePartitionStatement
import Theorems.Thm_GlobalTheory_smooth_genericFibre_closure_partition


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → ∀ C C' : Set X, C ∪ C' = f ⁻¹' {(⊥ : PrimeSpectrum R)} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by
  first | exact @GlobalTheory.smooth_genericFibre_closure_partition | exact GlobalTheory.smooth_genericFibre_closure_partition | (intros; apply GlobalTheory.smooth_genericFibre_closure_partition <;> assumption)
end _root_.GlobalTheory.T

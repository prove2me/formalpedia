-- Prove2me | solution 1 for GlobalTheory.T.closure_generic_fibre_clopen_split_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:50:41.470205+00:00
-- url     : https://prove2.me/submissions/dc9213ba-de5f-4c3f-80c6-abc90dc5d60f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosureGenericFibreClopenSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClosureGenericFibreClopenSplitStatement
import Theorems.Thm_GlobalTheory_closure_generic_fibre_clopen_split


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
theorem _root_.solution : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A], Algebra.Smooth R A → ∀ C C' : Set (PrimeSpectrum A), C ∪ C' = {r | r.asIdeal.comap (algebraMap R A) = ⊥} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by
  first | exact @GlobalTheory.closure_generic_fibre_clopen_split | exact GlobalTheory.closure_generic_fibre_clopen_split | (intros; apply GlobalTheory.closure_generic_fibre_clopen_split <;> assumption)
end _root_.GlobalTheory.T

-- Prove2me | solution 1 for GlobalTheory.SepPoint.aeval_mem_adjoin_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:44:35.673533+00:00
-- url     : https://prove2.me/submissions/dc2293cc-f35d-4a7a-b862-1714f12124fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegrallyClosedAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveElementSeparabilityCertificate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin
open GlobalTheory GlobalTheory.SepPoint
namespace GlobalTheory.SepPoint
theorem _root_.solution {k F : Type} [Field k] [Field F] [Algebra k F]
    (R : Subalgebra k F) (θ : F) (g : R[X]) :
    aeval θ g ∈ Algebra.adjoin k (insert θ (R : Set F)) := by
  rw [aeval_eq_sum_range]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (g.coeff i).2))
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) _)
end GlobalTheory.SepPoint

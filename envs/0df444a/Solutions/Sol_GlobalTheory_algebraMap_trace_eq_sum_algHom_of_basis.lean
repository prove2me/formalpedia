-- Prove2me | solution 1 for GlobalTheory.algebraMap_trace_eq_sum_algHom_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:38.08294+00:00
-- url     : https://prove2.me/submissions/b30c2a39-3a74-4422-bd4f-c88641b2e2f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_map_charpoly_leftMulMatrix_eq_prod_algHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
open GlobalTheory
variable {R S L ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing L] [IsDomain L]
  [Algebra R L] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) (x : S) :
    algebraMap R L (Algebra.trace R S x) = ∑ j, P j x := by
  have h := map_charpoly_leftMulMatrix_eq_prod_algHom e hP x
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_diagonal] at h
  rw [Algebra.trace_eq_matrix_trace e, ← Matrix.trace_diagonal,
    Matrix.trace_eq_neg_charpoly_nextCoeff (Matrix.diagonal _), ← h,
    ← Matrix.trace_eq_neg_charpoly_nextCoeff, AddMonoidHom.map_trace]
end GlobalTheory

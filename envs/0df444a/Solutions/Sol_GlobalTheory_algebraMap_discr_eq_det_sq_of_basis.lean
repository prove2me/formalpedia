-- Prove2me | solution 1 for GlobalTheory.algebraMap_discr_eq_det_sq_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:15:04.826294+00:00
-- url     : https://prove2.me/submissions/d8f2dee1-c1fe-4601-886d-b66836bd4132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_map_traceMatrix_eq_mul_transpose_of_basis

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
    (hP : Function.Injective P) (v : ι → S) :
    algebraMap R L (Algebra.discr R v) = (Matrix.of fun i j => P j (v i)).det ^ 2 := by
  rw [Algebra.discr_def, RingHom.map_det, RingHom.mapMatrix_apply,
    map_traceMatrix_eq_mul_transpose_of_basis e hP, Matrix.det_mul, Matrix.det_transpose, pow_two]
end GlobalTheory

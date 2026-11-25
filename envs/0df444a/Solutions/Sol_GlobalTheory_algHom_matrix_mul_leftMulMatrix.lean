-- Prove2me | solution 1 for GlobalTheory.algHom_matrix_mul_leftMulMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:19:06.091509+00:00
-- url     : https://prove2.me/submissions/ff3eeb29-5444-4000-9640-a4a7e789a765

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin

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
omit [IsDomain L]
namespace GlobalTheory
theorem _root_.solution (e : Basis ι R S) (P : ι → (S →ₐ[R] L)) (x : S) :
    (Matrix.of fun j i => P j (e i)) * (Algebra.leftMulMatrix e x).map (algebraMap R L) =
      Matrix.diagonal (fun j => P j x) * Matrix.of fun j i => P j (e i) := by
  ext j k
  rw [Matrix.diagonal_mul, Matrix.of_apply, ← map_mul, ← e.sum_repr (x * e k), map_sum,
    Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Matrix.of_apply, mul_comm]
end GlobalTheory

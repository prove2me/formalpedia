-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.gramOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:33.925285+00:00
-- url     : https://prove2.me/submissions/2a4f505d-eb93-49aa-b933-5a87cf2a661e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.BoundedBasis
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) :
    gramOf G v = Matrix.of v * G * ((Matrix.of v).map (IsCMField.complexConj E).toRingHom)ᵀ := by
  ext i k
  simp only [gramOf, herm, Matrix.of_apply, Matrix.mul_apply, Finset.sum_mul, transpose_apply,
    map_apply]
  exact Finset.sum_comm
end GlobalTheory.BoundedBasis

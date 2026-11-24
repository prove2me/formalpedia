-- Prove2me | solution 1 for GlobalTheory.topFormCoeff_topFormGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:47:08.638469+00:00
-- url     : https://prove2.me/submissions/8802df74-464a-486f-9bfd-b40015cf4076

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_GlobalTheory_topFormGen_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (V : Type*) {F : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F]
variable {V}
variable (F) {K : Type*} [CommRing K] [Algebra K V] [Algebra K F] [IsScalarTower K V F] {n : ℕ}
variable {F} (b : Basis (Fin n) V Ω[V⁄K])
omit [IsDomain V] [IsDiscreteValuationRing V]
namespace GlobalTheory
theorem _root_.solution : topFormCoeff F b (topFormGen F b) = 1 := by
  rw [topFormGen_eq, topFormCoeff, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    Basis.det_self]
end GlobalTheory

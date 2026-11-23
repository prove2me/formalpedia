-- Prove2me | solution 1 for GlobalTheory.fracKaehlerBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:14.326098+00:00
-- url     : https://prove2.me/submissions/1416a27c-895d-40cb-95f1-879b6c88341f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent

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
omit [IsDomain V] [IsDiscreteValuationRing V]
namespace GlobalTheory
theorem _root_.solution (b : Basis (Fin n) V Ω[V⁄K]) (k : Fin n) :
    fracKaehlerBasis F b k = KaehlerDifferential.map K K V F (b k) :=
  b.ofIsLocalizedModule_apply F V⁰ _ k
end GlobalTheory

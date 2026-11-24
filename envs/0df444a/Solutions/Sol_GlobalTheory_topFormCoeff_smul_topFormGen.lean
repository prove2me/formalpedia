-- Prove2me | solution 1 for GlobalTheory.topFormCoeff_smul_topFormGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:12.175384+00:00
-- url     : https://prove2.me/submissions/cd6e79d5-54bb-4d1d-8dec-470859a87ad9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_P2M_GlobalTheory_eq_lift_det_smul__Multi_7c34f112c031
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
theorem _root_.solution (ω : ⋀[F]^n Ω[F⁄K]) :
    topFormCoeff F b ω • topFormGen F b = ω := by
  rw [topFormGen_eq]
  exact (eq_lift_det_smul_ιMulti _ ω).symm
end GlobalTheory

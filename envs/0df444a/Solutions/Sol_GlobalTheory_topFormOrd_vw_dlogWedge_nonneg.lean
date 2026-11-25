-- Prove2me | solution 1 for GlobalTheory.topFormOrd_vw_dlogWedge_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:13.729938+00:00
-- url     : https://prove2.me/submissions/83153f09-5d06-4325-ba65-60b1377c5ac7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_GlobalTheory_dlogWedge_mem_regForms
import Theorems.Thm_GlobalTheory_topFormOrd_vw_nonneg_iff

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
namespace GlobalTheory
theorem _root_.solution (S : Finset (Fin n)) (x : Fin n → V)
    (hS : ∀ k ∈ S, IsUnit (x k)) :
    0 ≤ topFormOrd_vw F b (dlogWedge K S fun k => algebraMap V F (x k)) :=
  (topFormOrd_vw_nonneg_iff b _).mpr (dlogWedge_mem_regForms K S x hS)
end GlobalTheory

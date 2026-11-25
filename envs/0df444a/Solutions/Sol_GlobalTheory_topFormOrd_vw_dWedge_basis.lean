-- Prove2me | solution 1 for GlobalTheory.topFormOrd_vw_dWedge_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:13:35.611625+00:00
-- url     : https://prove2.me/submissions/9daf9567-3b8f-4c24-adfe-6b8a1fec8ab6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_GlobalTheory_formMap_dWedge
import Theorems.Thm_GlobalTheory_topFormOrd_vw_topFormGen

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
theorem _root_.solution (z : Fin n → V) (c : Basis (Fin n) V Ω[V⁄K])
    (hc : ∀ k, c k = D K V (z k)) :
    topFormOrd_vw F b (dWedge K fun k => algebraMap V F (z k)) = 0 := by
  rw [← topFormOrd_vw_topFormGen (F := F) b c, ← formMap_dWedge, topFormGen, dWedge, ← funext hc]
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.DiscrJacobianBlocks.det_eq_prod_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:27:48.833727+00:00
-- url     : https://prove2.me/submissions/ae3db22c-8320-4b5b-9c57-30f48a9effe6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrEqJacobianOfIntegralPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsFactorAssociatedJacobian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.DiscrJacobianBlocks
namespace GlobalTheory.DiscrJacobianBlocks
theorem _root_.solution {O Y : Type} [CommRing O] [DecidableEq Y] {d : ℕ} (p : Fin d → Y)
    (M : Matrix (Fin d) (Fin d) O) (hM : ∀ a a', p a ≠ p a' → M a a' = 0) :
    M.det = ∏ y ∈ Finset.univ.image p,
      (Matrix.of fun a a' : {a // p a = y} => M a.1 a'.1).det := by
  let _ : LinearOrder Y := @linearOrderOfSTO Y WellOrderingRel _ (Classical.decRel _)
  have hb : M.BlockTriangular p := fun a a' h => hM a a' (ne_of_gt h)
  have := hb.det
  convert this using 2
  rfl
end GlobalTheory.DiscrJacobianBlocks

-- Prove2me | solution 1 for GlobalTheory.SingleBlock.map_residue_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:57.167135+00:00
-- url     : https://prove2.me/submissions/9013a1e6-cdda-4cfe-95af-989795e56f3b

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_T2SpaceIsNonarchimedeanLocalFieldSingleBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate ValuativeRel Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F]
namespace GlobalTheory.SingleBlock
theorem _root_.solution (O : Type) [CommRing O] [IsLocalRing O] (n : Type) [Fintype n]
    [DecidableEq n] :
    Function.Surjective (GeneralLinearGroup.map (n := n) (IsLocalRing.residue O)) := by
  intro g
  let M : Matrix n n O := fun a b =>
    Function.surjInv (IsLocalRing.residue_surjective (R := O)) ((g : Matrix n n _) a b)
  have hM : M.map (IsLocalRing.residue O) = (g : Matrix n n _) := by
    ext a b
    exact Function.surjInv_eq _ _
  have hdet : IsUnit M.det := by
    have h1 : IsUnit (IsLocalRing.residue O M.det) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
      exact (isUnit_iff_isUnit_det _).1 g.isUnit
    exact (isUnit_map_iff (IsLocalRing.residue O) _).1 h1
  exact ⟨GeneralLinearGroup.mk'' M hdet, Units.ext hM⟩
end GlobalTheory.SingleBlock

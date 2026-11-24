-- Prove2me | solution 1 for GlobalTheory.JR.Step.det_embHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:11:12.996281+00:00
-- url     : https://prove2.me/submissions/4c2e90bb-8605-4264-bc4f-a2b979211a45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftMatch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step
variable {r : ℕ} {k : Type} [CommRing k]
namespace GlobalTheory.JR.Step
theorem _root_.solution (h : Matrix (Fin r) (Fin r) k) : (embHom r k h).det = h.det := by
  simp [embHom, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
end GlobalTheory.JR.Step

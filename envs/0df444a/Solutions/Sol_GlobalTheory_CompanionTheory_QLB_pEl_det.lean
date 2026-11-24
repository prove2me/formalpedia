-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLB.pEl_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:38:37.920909+00:00
-- url     : https://prove2.me/submissions/5736fc51-2686-4bc3-9f43-8c20e2e95fe4

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicElementBlocks
import Theorems.Thm_GlobalTheory_CompanionTheory_QLB_pEl_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLB
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QLB
theorem _root_.solution {r c : ℕ} (m₁ : GL (Fin r) F) (B : Matrix (Fin r) (Fin c) F) (m₂ : GL (Fin c) F) :
    (pEl m₁ B m₂ : Matrix (Fin (r + c)) (Fin (r + c)) F).det =
      (m₁ : Matrix (Fin r) (Fin r) F).det * (m₂ : Matrix (Fin c) (Fin c) F).det := by
  rw [pEl_coe, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
end GlobalTheory.CompanionTheory.QLB

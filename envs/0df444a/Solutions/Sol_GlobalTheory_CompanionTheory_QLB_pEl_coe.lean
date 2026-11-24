-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLB.pEl_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:56:34.992636+00:00
-- url     : https://prove2.me/submissions/d76db0b2-1571-4f3b-ba2a-b75f97b6adbc

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicElementBlocks

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
    (pEl m₁ B m₂ : Matrix (Fin (r + c)) (Fin (r + c)) F) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (m₁ : Matrix (Fin r) (Fin r) F) B 0 (m₂ : Matrix (Fin c) (Fin c) F)) := rfl
end GlobalTheory.CompanionTheory.QLB

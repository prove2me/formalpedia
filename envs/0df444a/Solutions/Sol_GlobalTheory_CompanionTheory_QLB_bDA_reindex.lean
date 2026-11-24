-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLB.bDA_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:38:34.256274+00:00
-- url     : https://prove2.me/submissions/eed86b63-bbd6-4ba9-bb13-195b7b67271d

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
variable {r d c : ℕ} (A : Matrix (Fin r) (Fin r) F) (B : Matrix (Fin r) (Fin c) F)
  (C : Matrix (Fin d) (Fin r) F) (D : Matrix (Fin d) (Fin c) F)
namespace GlobalTheory.CompanionTheory.QLB
theorem _root_.solution : bDA (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)) = C := by
  ext i j; simp [bDA]
end GlobalTheory.CompanionTheory.QLB

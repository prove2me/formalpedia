-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.word_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:23.239444+00:00
-- url     : https://prove2.me/submissions/2c13ade5-1f07-4d95-8382-d6894b428f5a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnalyticWord
variable {V H : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type}
namespace GlobalTheory.CompanionTheory.AnalyticWord
theorem _root_.solution (Z : ι → Module.End ℂ V) (i : ι) (l : List ι) :
    word Z (i :: l) = Z i * word Z l := by simp [word]
end GlobalTheory.CompanionTheory.AnalyticWord

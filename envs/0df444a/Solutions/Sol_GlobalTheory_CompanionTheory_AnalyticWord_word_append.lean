-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.word_append
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:42.994085+00:00
-- url     : https://prove2.me/submissions/191af8ea-a06e-4118-800b-8644bd4d57b8

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
theorem _root_.solution (Z : ι → Module.End ℂ V) (p q : List ι) :
    word Z (p ++ q) = word Z p * word Z q := by simp [word, List.prod_append]
end GlobalTheory.CompanionTheory.AnalyticWord

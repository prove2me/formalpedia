-- Prove2me | solution 1 for OAI.KadisonSimilarity.arcWidth_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:20:33.428258+00:00
-- url     : https://prove2.me/submissions/3e67b618-3966-4ba8-b095-5d6e4b7b9ed1

import Mathlib
import Definitions.Def_OAIQ075A006

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_HankelBounds
attribute [-instance] _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite Hankel test in the similarity manuscript

The coefficients here are the actual Fourier coefficients of the narrow-arc
function in Section `hankel`: `sin (l θ) / (π l)`, with `θ = 1/(2N)`.
The lower bound uses the constant vector in the first `N` coordinates.
No assertion about the free-product construction is assumed here.
-/

noncomputable section

namespace KadisonSimilarity

open Finset

theorem arcWidth_pos_oai {N : ℕ} (hN : 0 < N) : 0 < arcWidth N := by
  unfold arcWidth
  positivity

end KadisonSimilarity

end

end OAI
end

theorem solution : type_of% @OAI.KadisonSimilarity.arcWidth_pos_oai := @OAI.KadisonSimilarity.arcWidth_pos_oai

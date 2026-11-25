-- Prove2me | solution 1 for GroundTheory.Arith.Etale.openInclLE_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:07:21.249411+00:00
-- url     : https://prove2.me/submissions/3fd19923-d211-49af-8f9e-56f160673f1f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohPresheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
variable {X : Scheme.{u}} (F : X.Modules) (U : X.Etale)
namespace GroundTheory.Arith.Etale
theorem _root_.solution {O' O : U.left.Opens} (h : O' ≤ O) :
    (openInclLE U h).left = U.left.homOfLE h := rfl
end GroundTheory.Arith.Etale
